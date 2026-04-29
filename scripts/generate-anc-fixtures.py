#!/usr/bin/env python3
"""Generate PNG fixture files used by Bitmap.Tests for ancillary-chunk handling.

Each fixture starts from the same 4x4 RGB pixel matrix (so the decoder can be
checked against a fixed expected pattern), then differs only in which chunks
are present between IHDR and IEND. Re-running the script is idempotent.

Run from the repo root:

    python3 scripts/generate-anc-fixtures.py
"""

import binascii
import os
import struct
import sys
import zlib

# --- shared 4x4 RGB pattern (24 bytes/row + 1 filter byte = 13 bytes/row)
WIDTH = 4
HEIGHT = 4
PIXELS = bytes(
    [
        # row 0: red, green, blue, white
        255, 0, 0,   0, 255, 0,   0, 0, 255,   255, 255, 255,
        # row 1: black, gray-128, gray-192, gray-64
        0, 0, 0,   128, 128, 128,   192, 192, 192,   64, 64, 64,
        # row 2: cyan, magenta, yellow, orange
        0, 255, 255,   255, 0, 255,   255, 255, 0,   255, 128, 0,
        # row 3: dark-red, dark-green, dark-blue, mid-gray
        128, 0, 0,   0, 128, 0,   0, 0, 128,   100, 100, 100,
    ]
)
assert len(PIXELS) == WIDTH * HEIGHT * 3

PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))


def make_chunk(chunk_type: bytes, data: bytes) -> bytes:
    """Encode one PNG chunk: length || type || data || crc32(type||data)."""
    if len(chunk_type) != 4:
        raise ValueError(f"chunk type must be 4 bytes, got {chunk_type!r}")
    crc = binascii.crc32(chunk_type + data) & 0xFFFFFFFF
    return struct.pack(">I", len(data)) + chunk_type + data + struct.pack(">I", crc)


def make_chunk_bad_crc(chunk_type: bytes, data: bytes) -> bytes:
    """Same as make_chunk but with the CRC deliberately corrupted by flipping one bit."""
    correct = binascii.crc32(chunk_type + data) & 0xFFFFFFFF
    bad = correct ^ 0x1
    return struct.pack(">I", len(data)) + chunk_type + data + struct.pack(">I", bad)


def make_ihdr() -> bytes:
    # 8-bit RGB, no compression/filter/interlace variation
    return make_ihdr_for(WIDTH, HEIGHT, 2)


def make_ihdr_for(width: int, height: int, color_type: int) -> bytes:
    # 8-bit samples, no compression/filter/interlace variation
    return make_chunk(
        b"IHDR",
        struct.pack(">IIBBBBB", width, height, 8, color_type, 0, 0, 0),
    )


def make_iend() -> bytes:
    return make_chunk(b"IEND", b"")


def deflate_with_filter_zero() -> bytes:
    """Build the IDAT payload: each row prefixed by filter type 0 (None)."""
    return deflate_pixels_with_filter_zero(WIDTH, HEIGHT, 3, PIXELS)


def deflate_pixels_with_filter_zero(width: int, height: int, channels: int, pixels: bytes) -> bytes:
    """Build an IDAT payload from interleaved pixels using filter type 0."""
    raw = b""
    row_bytes = width * channels
    for y in range(height):
        row_start = y * row_bytes
        raw += b"\x00" + pixels[row_start : row_start + row_bytes]
    return zlib.compress(raw)


def make_idat() -> bytes:
    return make_chunk(b"IDAT", deflate_with_filter_zero())


def make_gray_idat() -> bytes:
    gray_pixels = bytes(
        [
            0, 64, 128, 255,
            32, 96, 160, 224,
            16, 80, 144, 208,
            48, 112, 176, 240,
        ]
    )
    return make_chunk(b"IDAT", deflate_pixels_with_filter_zero(WIDTH, HEIGHT, 1, gray_pixels))


def make_idats_split(n: int) -> bytes:
    """Split the same compressed IDAT bytes across n chunks of (almost) equal size."""
    payload = deflate_with_filter_zero()
    if n < 1:
        raise ValueError("n must be >= 1")
    out = b""
    chunk = max(1, len(payload) // n)
    pos = 0
    for i in range(n):
        end = len(payload) if i == n - 1 else min(pos + chunk, len(payload))
        out += make_chunk(b"IDAT", payload[pos:end])
        pos = end
    return out


def write(name: str, body: bytes) -> None:
    path = os.path.join(REPO_ROOT, name)
    with open(path, "wb") as f:
        f.write(PNG_SIGNATURE + body)
    print(f"wrote {name} ({os.path.getsize(path)} bytes)")


def main() -> int:
    # 1. RGB PNG with gAMA + pHYs chunks before IDAT (tolerated metadata).
    gama = make_chunk(b"gAMA", struct.pack(">I", 45455))  # 1.0/2.2
    phys = make_chunk(b"pHYs", struct.pack(">IIB", 2835, 2835, 1))  # 72 DPI, meter
    write("test_anc_meta.png", make_ihdr() + gama + phys + make_idat() + make_iend())

    # 2. RGB PNG with a tEXt chunk (Comment=test).
    text = make_chunk(b"tEXt", b"Comment\x00test")
    write("test_anc_text.png", make_ihdr() + text + make_idat() + make_iend())

    # 3. RGB PNG split across 3 IDAT chunks (must concatenate and decode the same).
    write("test_anc_multi_idat.png", make_ihdr() + make_idats_split(3) + make_iend())

    # 4. RGB PNG with an unknown ancillary chunk "myCh" (lowercase first byte
    #    => ancillary, decoder must skip it after CRC validation).
    unknown_anc = make_chunk(b"myCh", b"unknown ancillary payload")
    write(
        "test_anc_unknown_anc.png",
        make_ihdr() + unknown_anc + make_idat() + make_iend(),
    )

    # 5. RGB PNG with an unknown critical chunk "MyCh" (uppercase first byte
    #    => critical, decoder must reject).
    unknown_crit = make_chunk(b"MyCh", b"unknown critical payload")
    write(
        "test_anc_unknown_critical.png",
        make_ihdr() + unknown_crit + make_idat() + make_iend(),
    )

    # 6. RGB PNG with a tRNS chunk — metadata-aware RGBA decode applies alpha.
    trns = make_chunk(b"tRNS", struct.pack(">HHH", 0, 0, 0))  # transparent black
    write("test_anc_trns.png", make_ihdr() + trns + make_idat() + make_iend())

    # 7. RGB PNG with bKGD — metadata preserved by the metadata-aware decoder.
    bkgd_rgb = make_chunk(b"bKGD", struct.pack(">HHH", 100, 100, 100))
    write("test_anc_bkgd_rgb.png", make_ihdr() + bkgd_rgb + make_idat() + make_iend())

    # 8. RGB PNG with both tRNS and bKGD — metadata-aware RGB decode composites
    #    the transparent color over the suggested background.
    write("test_anc_trns_bkgd.png", make_ihdr() + trns + bkgd_rgb + make_idat() + make_iend())

    # 9. RGBA PNG with bKGD — metadata-aware RGB decode composites alpha over
    #    the suggested background.
    bkgd_blue = make_chunk(b"bKGD", struct.pack(">HHH", 0, 0, 255))
    rgba_alpha_pixels = bytes([255, 0, 0, 128] * (WIDTH * HEIGHT))
    rgba_alpha_idat = make_chunk(b"IDAT", deflate_pixels_with_filter_zero(WIDTH, HEIGHT, 4, rgba_alpha_pixels))
    write("test_anc_rgba_bkgd.png", make_ihdr_for(WIDTH, HEIGHT, 6) + bkgd_blue + rgba_alpha_idat + make_iend())

    # 10. Grayscale PNG with bKGD — metadata preserved by the metadata-aware decoder.
    bkgd_gray = make_chunk(b"bKGD", struct.pack(">H", 64))
    write(
        "test_anc_bkgd_gray.png",
        make_ihdr_for(WIDTH, HEIGHT, 0) + bkgd_gray + make_gray_idat() + make_iend(),
    )

    # 11. Invalid tRNS/bKGD ordering and payload-shape cases.
    trns_bad_len = make_chunk(b"tRNS", b"\x00")
    write("test_anc_trns_bad_len.png", make_ihdr() + trns_bad_len + make_idat() + make_iend())
    write("test_anc_trns_after_idat.png", make_ihdr() + make_idat() + trns + make_iend())
    write("test_anc_trns_duplicate.png", make_ihdr() + trns + trns + make_idat() + make_iend())
    plte = make_chunk(b"PLTE", b"\x00\x00\x00")
    write("test_anc_plte_after_trns.png", make_ihdr() + trns + plte + make_idat() + make_iend())
    bkgd_bad_len = make_chunk(b"bKGD", b"\x00")
    write("test_anc_bkgd_bad_len.png", make_ihdr() + bkgd_bad_len + make_idat() + make_iend())
    write("test_anc_bkgd_after_idat.png", make_ihdr() + make_idat() + bkgd_rgb + make_iend())
    write("test_anc_bkgd_duplicate.png", make_ihdr() + bkgd_rgb + bkgd_rgb + make_idat() + make_iend())
    write("test_anc_plte_after_bkgd.png", make_ihdr() + bkgd_rgb + plte + make_idat() + make_iend())
    trns_rgba = make_chunk(b"tRNS", struct.pack(">HHH", 0, 0, 0))
    rgba_pixels = bytes([255, 0, 0, 255] * (WIDTH * HEIGHT))
    rgba_idat = make_chunk(b"IDAT", deflate_pixels_with_filter_zero(WIDTH, HEIGHT, 4, rgba_pixels))
    write("test_anc_trns_rgba.png", make_ihdr_for(WIDTH, HEIGHT, 6) + trns_rgba + rgba_idat + make_iend())

    # 12. RGB PNG with an sBIT chunk — pixel-affecting, decoder rejects.
    sbit = make_chunk(b"sBIT", b"\x08\x08\x08")
    write("test_anc_sbit.png", make_ihdr() + sbit + make_idat() + make_iend())

    # 13. RGB PNG whose IDAT chunk has a bad CRC32 — decoder rejects.
    bad_idat = make_chunk_bad_crc(b"IDAT", deflate_with_filter_zero())
    write("test_anc_bad_crc.png", make_ihdr() + bad_idat + make_iend())

    return 0


if __name__ == "__main__":
    sys.exit(main())
