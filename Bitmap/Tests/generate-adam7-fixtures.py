#!/usr/bin/env python3
"""Generate PNG fixtures used by Bitmap.Tests for Adam7 interlace decoding.

Run from the repo root:

    python3 Bitmap/Tests/generate-adam7-fixtures.py
"""

import binascii
import os
import struct
import zlib

FIXTURE_DIR = os.path.abspath(os.path.dirname(__file__))
PNG_SIGNATURE = b"\x89PNG\r\n\x1a\n"
ADAM7_PASSES = [
    (0, 0, 8, 8),
    (4, 0, 8, 8),
    (0, 4, 4, 8),
    (2, 0, 4, 4),
    (0, 2, 2, 4),
    (1, 0, 2, 2),
    (0, 1, 1, 2),
]


def u8(n: int) -> int:
    return n & 0xFF


def u16be(n: int) -> bytes:
    return struct.pack(">H", n & 0xFFFF)


def make_chunk(chunk_type: bytes, data: bytes) -> bytes:
    crc = binascii.crc32(chunk_type + data) & 0xFFFFFFFF
    return struct.pack(">I", len(data)) + chunk_type + data + struct.pack(">I", crc)


def make_ihdr(width: int, height: int, color_type: int, bit_depth: int, interlace: int = 1) -> bytes:
    return make_chunk(
        b"IHDR",
        struct.pack(">IIBBBBB", width, height, bit_depth, color_type, 0, 0, interlace),
    )


def make_png(width: int, height: int, color_type: int, bit_depth: int, raw: bytes,
             ancillary: bytes = b"", interlace: int = 1) -> bytes:
    return (
        PNG_SIGNATURE
        + make_ihdr(width, height, color_type, bit_depth, interlace)
        + ancillary
        + make_chunk(b"IDAT", zlib.compress(raw))
        + make_chunk(b"IEND", b"")
    )


def pass_dim(full: int, start: int, step: int) -> int:
    if start >= full:
        return 0
    return ((full - 1 - start) // step) + 1


def paeth(a: int, b: int, c: int) -> int:
    p = a + b - c
    pa = abs(p - a)
    pb = abs(p - b)
    pc = abs(p - c)
    if pa <= pb and pa <= pc:
        return a
    if pb <= pc:
        return b
    return c


def filter_row(row: bytes, prev: bytes, bpp: int, filter_type: int) -> bytes:
    out = bytearray()
    for i, value in enumerate(row):
        left = row[i - bpp] if i >= bpp else 0
        up = prev[i] if i < len(prev) else 0
        up_left = prev[i - bpp] if i >= bpp and i < len(prev) else 0
        if filter_type == 0:
            encoded = value
        elif filter_type == 1:
            encoded = value - left
        elif filter_type == 2:
            encoded = value - up
        elif filter_type == 3:
            encoded = value - ((left + up) // 2)
        elif filter_type == 4:
            encoded = value - paeth(left, up, up_left)
        else:
            raise ValueError(filter_type)
        out.append(u8(encoded))
    return bytes(out)


def sample8(x: int, y: int, salt: int) -> int:
    return u8(x * 17 + y * 31 + salt)


def sample16(x: int, y: int, salt: int) -> int:
    return (x * 4099 + y * 257 + salt) & 0xFFFF


def pixel_bytes(color_type: int, bit_depth: int, x: int, y: int) -> bytes:
    if bit_depth == 8:
        if color_type == 0:
            return bytes([sample8(x, y, 3)])
        if color_type == 2:
            return bytes([sample8(x, y, 5), sample8(x, y, 17), sample8(x, y, 29)])
        if color_type == 4:
            return bytes([sample8(x, y, 7), sample8(x, y, 113)])
        if color_type == 6:
            return bytes([sample8(x, y, 11), sample8(x, y, 23), sample8(x, y, 37), sample8(x, y, 151)])
    if bit_depth == 16:
        if color_type == 0:
            return u16be(sample16(x, y, 0x1234))
        if color_type == 2:
            return (
                u16be(sample16(x, y, 0x1001))
                + u16be(sample16(x, y, 0x3003))
                + u16be(sample16(x, y, 0x5005))
            )
    raise ValueError((color_type, bit_depth))


def bytes_per_pixel(color_type: int, bit_depth: int) -> int:
    channels = {0: 1, 2: 3, 4: 2, 6: 4}[color_type]
    return channels * (2 if bit_depth == 16 else 1)


def adam7_raw(width: int, height: int, color_type: int, bit_depth: int,
              varied_filters: bool = False) -> bytes:
    bpp = bytes_per_pixel(color_type, bit_depth)
    out = bytearray()
    for pass_index, (start_x, start_y, step_x, step_y) in enumerate(ADAM7_PASSES):
        pass_width = pass_dim(width, start_x, step_x)
        pass_height = 0 if pass_width == 0 else pass_dim(height, start_y, step_y)
        prev = b""
        for pass_y in range(pass_height):
            y = start_y + pass_y * step_y
            row = b"".join(
                pixel_bytes(color_type, bit_depth, start_x + pass_x * step_x, y)
                for pass_x in range(pass_width)
            )
            filter_type = (pass_index + pass_y) % 5 if varied_filters else 0
            out.append(filter_type)
            out.extend(filter_row(row, prev, bpp, filter_type))
            prev = row
    return bytes(out)


def write(name: str, data: bytes) -> None:
    path = os.path.join(FIXTURE_DIR, name)
    with open(path, "wb") as f:
        f.write(data)
    print(f"wrote {path} ({len(data)} bytes)")


def main() -> None:
    write("test_adam7_rgb8_9x9_filters.png", make_png(9, 9, 2, 8, adam7_raw(9, 9, 2, 8, True)))
    write("test_adam7_gray8_2x3.png", make_png(2, 3, 0, 8, adam7_raw(2, 3, 0, 8)))
    write("test_adam7_grayalpha8_9x9.png", make_png(9, 9, 4, 8, adam7_raw(9, 9, 4, 8)))
    write("test_adam7_rgba8_1x1.png", make_png(1, 1, 6, 8, adam7_raw(1, 1, 6, 8)))
    write("test_adam7_rgb16_9x9.png", make_png(9, 9, 2, 16, adam7_raw(9, 9, 2, 16)))
    write("test_adam7_gray16_2x3.png", make_png(2, 3, 0, 16, adam7_raw(2, 3, 0, 16)))

    trns = make_chunk(
        b"tRNS",
        u16be(sample8(0, 0, 5)) + u16be(sample8(0, 0, 17)) + u16be(sample8(0, 0, 29)),
    )
    bkgd = make_chunk(b"bKGD", u16be(10) + u16be(20) + u16be(30))
    write("test_adam7_trns_bkgd_rgb8.png", make_png(2, 3, 2, 8, adam7_raw(2, 3, 2, 8), trns + bkgd))

    write("test_adam7_interlace2.png", make_png(2, 3, 2, 8, adam7_raw(2, 3, 2, 8), interlace=2))

    full_raw = adam7_raw(9, 9, 2, 8)
    write("test_adam7_truncated.png", make_png(9, 9, 2, 8, full_raw[:-1]))


if __name__ == "__main__":
    main()
