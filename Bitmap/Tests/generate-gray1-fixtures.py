#!/usr/bin/env python3
import binascii
import struct
import zlib
from pathlib import Path


OUT = Path(__file__).resolve().parent
SIG = b"\x89PNG\r\n\x1a\n"


def chunk(kind: bytes, data: bytes) -> bytes:
    return struct.pack(">I", len(data)) + kind + data + struct.pack(">I", binascii.crc32(kind + data) & 0xFFFFFFFF)


def pixel_on(x: int, y: int) -> bool:
    return ((x * 3 + y * 5 + x * y) % 7) < 3


def pack_bits(bits):
    bits = list(bits)
    out = bytearray((len(bits) + 7) // 8)
    for i, bit in enumerate(bits):
        if bit:
            out[i // 8] |= 1 << (7 - (i % 8))
    return bytes(out)


def gray1_row(w: int, y: int) -> bytes:
    return pack_bits(pixel_on(x, y) for x in range(w))


def filt_row(kind: int, row: bytes, prev: bytes, bpp: int = 1) -> bytes:
    out = bytearray()
    for i, val in enumerate(row):
        left = row[i - bpp] if i >= bpp else 0
        up = prev[i] if i < len(prev) else 0
        up_left = prev[i - bpp] if i >= bpp and i < len(prev) else 0
        if kind == 0:
            pred = 0
        elif kind == 1:
            pred = left
        elif kind == 2:
            pred = up
        elif kind == 3:
            pred = (left + up) // 2
        elif kind == 4:
            p = left + up - up_left
            pa = abs(p - left)
            pb = abs(p - up)
            pc = abs(p - up_left)
            pred = left if pa <= pb and pa <= pc else up if pb <= pc else up_left
        else:
            raise ValueError(kind)
        out.append((val - pred) & 0xFF)
    return bytes(out)


def raw_noninterlaced(w: int, h: int, filters=None, truncate: int = 0) -> bytes:
    raw = bytearray()
    prev = b""
    for y in range(h):
        row = gray1_row(w, y)
        f = 0 if filters is None else filters[y % len(filters)]
        raw.append(f)
        raw.extend(filt_row(f, row, prev))
        prev = row
    if truncate:
        raw = raw[:-truncate]
    return bytes(raw)


PASSES = [
    (0, 0, 8, 8),
    (4, 0, 8, 8),
    (0, 4, 4, 8),
    (2, 0, 4, 4),
    (0, 2, 2, 4),
    (1, 0, 2, 2),
    (0, 1, 1, 2),
]


def pass_dim(full: int, start: int, step: int) -> int:
    if start >= full:
        return 0
    return ((full - 1 - start) // step) + 1


def raw_adam7(w: int, h: int, filters=(0, 1, 2, 3, 4)) -> bytes:
    raw = bytearray()
    fidx = 0
    for sx, sy, dx, dy in PASSES:
        pw = pass_dim(w, sx, dx)
        ph = 0 if pw == 0 else pass_dim(h, sy, dy)
        prev = b""
        for py in range(ph):
            y = sy + py * dy
            bits = [pixel_on(sx + px * dx, y) for px in range(pw)]
            row = pack_bits(bits)
            f = filters[fidx % len(filters)]
            fidx += 1
            raw.append(f)
            raw.extend(filt_row(f, row, prev))
            prev = row
    return bytes(raw)


def png(w: int, h: int, bit_depth: int, color_type: int, raw: bytes, *, interlace=0, extra=()) -> bytes:
    ihdr = struct.pack(">IIBBBBB", w, h, bit_depth, color_type, 0, 0, interlace)
    return SIG + chunk(b"IHDR", ihdr) + b"".join(extra) + chunk(b"IDAT", zlib.compress(raw)) + chunk(b"IEND", b"")


def write(name: str, data: bytes) -> None:
    (OUT / name).write_bytes(data)


def main() -> None:
    for w in [1, 7, 8, 9, 17]:
        write(f"test_gray1_w{w}.png", png(w, 3, 1, 0, raw_noninterlaced(w, 3)))
    write("test_gray1_filters.png", png(17, 5, 1, 0, raw_noninterlaced(17, 5, [0, 1, 2, 3, 4])))
    write("test_gray1_adam7.png", png(9, 9, 1, 0, raw_adam7(9, 9), interlace=1))
    write(
        "test_gray1_trns_bkgd.png",
        png(
            9,
            3,
            1,
            0,
            raw_noninterlaced(9, 3),
            extra=(chunk(b"tRNS", b"\x00\x01"), chunk(b"bKGD", b"\x00\x00")),
        ),
    )
    write("test_gray1_invalid_rgb1.png", png(3, 3, 1, 2, raw_noninterlaced(3, 3)))
    write("test_gray1_truncated.png", png(9, 3, 1, 0, raw_noninterlaced(9, 3, truncate=1)))


if __name__ == "__main__":
    main()
