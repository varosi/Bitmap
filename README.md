# bitmap

Lean 4 bitmap image utilities with PNG encode/decode support, plus a small widget for visualization.

This library has proofs about:
- putPixel and getPixel correspondence (Bitmap.Lemmas.putPixel_getPixel);
- PNG format encode and decode correspondence (Bitmap.Lemmas.decodeBitmap_encodeBitmap);
- PNG chunk validation properties for CRC checks and chunk-order state transitions
  (`readChunk_rejects_crc_mismatch`, `readChunk_success_crc_matches`,
  `parsePngLoopFuel_rejects_non_ihdr_before_header`,
  `parsePngLoopFuel_rejects_duplicate_ihdr`,
  `parsePngLoopFuel_rejects_plte_after_plte_or_idat`,
  `parsePngLoopFuel_rejects_idat_after_closed_idat`,
  `parsePngLoopFuel_rejects_nonempty_iend`,
  `parsePngLoopFuel_rejects_iend_before_idat`,
  `parsePngLoopFuel_rejects_trailing_after_iend`,
  `parsePngLoopFuel_rejects_unknown_critical`,
  `parsePngLoopFuel_rejects_tRNS`,
  `parsePngLoopFuel_rejects_sBIT`,
  `parsePngLoopFuel_ignores_ancillary_before_idat`,
  `parsePngLoopFuel_idat_appends_when_open`);
- dynamic DEFLATE decoder correctness for proof-specified dynamic table reads,
  payload traces, dynamic-only multi-block streams, and zlib envelopes
  (`dynamicTableReaderSpec_readDynamicTables`, `dynamicPayloadTrace_decode_correct`,
  `dynamicDeflateStreamSpec_decode_correct`, `zlibDecompress_dynamicStreamSpec_correct`);
- there are no buffer overflows;
- PNG encode and decode are total functions.

## Proof Coverage Limits

The PNG round-trip proofs are encoder-to-decoder proofs for streams produced by this
library. They do not yet prove that the decoder accepts every valid PNG file or every
valid zlib/DEFLATE stream produced by another implementation.

The dynamic DEFLATE proof now has a generic operational spec layer: successful
`readDynamicTablesSpec?` parses project to the runtime table reader, any validated
`DynamicPayloadTrace` decodes to the specified bytes, `DynamicDeflateStreamSpec`
covers dynamic-only multi-block streams through `BFINAL`, and
`ZlibDynamicStreamSpec` adds the zlib header and Adler-32 trailer checks. The
concrete dynamic-fast encoder proof is a regression client of that generic layer.

This is still not a standalone RFC-1951 grammar/completeness theorem independent of
the runtime parser, nor a single mixed stored/fixed/dynamic block-stream theorem.
The proof-level dynamic table boundary delegates bit-level header parsing to
`readDynamicTables`; runtime tests cover code-length repeats `16`, `17`, and `18`,
repeat overflow shape, literal-only zero-distance blocks, LZ77 matches, and dynamic
multi-block fixtures.

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
| PNG structure | 8-byte signature, `IHDR` first, multiple consecutive `IDAT` chunks accepted and concatenated, `IEND` last, required `PLTE` ordering checks, rejects unknown critical chunks, compression/filter method ≠ 0, and interlace ≠ 0 |
| Tolerated ancillary chunks | `gAMA`, `cHRM`, `sRGB`, `iCCP`, `pHYs`, `tEXt`, `zTXt`, `iTXt`, `tIME`, `bKGD`, `hIST`, `sPLT`, plus any unknown chunk type whose first byte is lowercase — CRC-validated and skipped without affecting decoded pixels |
| Integrity | CRC-32 verified for every parsed chunk; mismatch rejects the entire input. Adler-32 verified at end of zlib stream |

### Not supported

- Bit depths other than 8 (1, 2, 4, 16)
- Color type 3 (palette / `PLTE`) and color type 4 (gray + alpha)
- Adam7 interlacing
- `tRNS` and `sBIT` chunks — explicitly **rejected** (decoder returns `none`) rather than silently ignored, to avoid the silent-corruption hazard of dropping transparency or precision metadata that affects pixel semantics
- Unknown critical chunks (any chunk type whose first byte is uppercase and not `IHDR`/`PLTE`/`IDAT`/`IEND`) — rejected per the PNG spec
- Reading-back of ancillary chunk **content** (`gAMA`, `tEXt`, etc.) — the chunks are validated and skipped; the decoder produces only the pixel matrix, not metadata
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
