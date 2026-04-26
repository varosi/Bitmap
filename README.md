# bitmap

Lean 4 bitmap image utilities with PNG encode/decode support, plus a small widget for visualization.

This library have proofs about:
- putPixel and getPixel correspondence (Bitmap.Lemmas.putPixel_getPixel);
- PNG format encode and decode correspondence (Bitmap.Lemmas.decodeBitmap_encodeBitmap);
- there are no buffer overflows;
- PNG encode and decode are total functions.

## Proof Coverage Limits

The PNG round-trip proofs are encoder-to-decoder proofs for streams produced by this
library. They do not yet prove that the decoder accepts every valid PNG file or every
valid zlib/DEFLATE stream produced by another implementation.

In particular, the dynamic DEFLATE proof currently covers the concrete dynamic block
shape emitted by the library's dynamic-fast encoder: a dynamic block header whose
Huffman tables reconstruct the fixed literal/length and distance tables, followed by
the proven fixed-style payload. This exercises the dynamic table reader and dynamic
block dispatch, but it is not a full DEFLATE specification proof for arbitrary valid
dynamic Huffman tables, all valid code-length repeat encodings, or all valid dynamic
multi-block streams.

Runtime decoding is broader than the current proof boundary: the decoder has a
general dynamic-table reader and compressed-block loop. The missing work is a formal
specification of arbitrary valid dynamic DEFLATE streams and a proof that the runtime
decoder implements that specification.

## Supported PNG features

The encoder and decoder target a deliberately narrow PNG subset — the one for
which the library carries full round-trip correctness proofs.

### Encoder

| Area | Support |
|---|---|
| Color types | `0` Grayscale, `2` RGB, `6` RGBA |
| Bit depth | 8 bits per channel |
| Pixel formats | `PixelGray8`, `PixelRGB8`, `PixelRGBA8` |
| Filter type | `0` (None) only — every encoded row is written with filter byte `0x00` |
| Compression modes | `.stored` (uncompressed DEFLATE), `.fixed` (fixed-Huffman with LZ77 distance-1 run encoding), `.dynamic` (dynamic-block header; payload currently delegates to fixed-Huffman) |
| Interlace | None (no Adam7) |
| Chunks emitted | `IHDR`, one `IDAT`, `IEND` — no ancillary chunks |
| Integrity | CRC-32 per chunk, Adler-32 in the zlib trailer |
| Dimension limits | width and height each `< 2^32`, enforced by `encodeBitmapChecked` |

### Decoder

| Area | Support |
|---|---|
| Color types | `0`, `2`, `6` (palette `3` and gray+alpha `4` rejected) |
| Bit depth | 8 bits per channel only |
| Filter types | All five reconstructed: `0` None, `1` Sub, `2` Up, `3` Average, `4` Paeth |
| Compression | `inflateStored` tried first, then fixed- and dynamic-Huffman zlib streams (full `HLIT`/`HDIST`/`HCLEN` + code-length-code + literal/length and distance tables) |
| LZ77 | Length codes 257–285 and distance codes 0–29 with extra bits; `copyDistance` supports overlap (distance < length) |
| Color conversion | RGB PNGs can be decoded into `BitmapRGBA8` (fills α = 255) and RGBA PNGs into `BitmapRGB8` (drops alpha) |
| PNG structure | 8-byte signature, `IHDR` + `IDAT` + `IEND`, rejects compression/filter method ≠ 0 and interlace ≠ 0 |
| Integrity | Adler-32 verified at end of stream; chunk layout enforced by length bounds |

### Not supported

- Bit depths other than 8 (1, 2, 4, 16)
- Color type 3 (palette / `PLTE`) and color type 4 (gray + alpha)
- Adam7 interlacing
- Ancillary chunks (`tRNS`, `gAMA`, `sRGB`, `cHRM`, `pHYs`, `tEXt`, `zTXt`, `iTXt`, `sBIT`, `bKGD`, `hIST`, `sPLT`, `tIME`)
- Encoder-side filter selection (always emits filter 0)
- Genuinely-distinct dynamic-Huffman encoding — `.dynamic` emits a dynamic-block header but delegates the deflate payload to fixed-Huffman

## Usage

```lean
import Bitmap
```

## Tests

```sh
lake test
```
