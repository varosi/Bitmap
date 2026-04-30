# bitmap

Lean 4 bitmap image utilities with PNG encode/decode support, plus a small widget for visualization.
The widget accepts the supported 8-bit bitmap formats and displays 16-bit bitmap
formats by downsampling each channel to its high byte for browser canvas output.

This library has proofs about:
- putPixel and getPixel correspondence (Bitmap.Lemmas.putPixel_getPixel);
- PNG format encode and decode correspondence for `PixelGray8`, `PixelRGB8`,
  `PixelRGBA8`, `PixelGrayAlpha8`, `PixelGray16`, `PixelRGB16`,
  `PixelRGBA16`, and `PixelGrayAlpha16`
  (Bitmap.Lemmas.decodeBitmap_encodeBitmap);
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
  `parseTrnsData_rejects_grayAlpha8`,
  `parseTrnsData_rejects_grayAlpha16`,
  `parseTrnsData_accepts_gray16`,
  `parseTrnsData_accepts_rgb16`,
  `parsePngLoopFuel_rejects_sBIT`,
  `parsePngLoopFuelWithMetadata_accepts_tRNS`,
  `parsePngLoopFuelWithMetadata_accepts_bKGD`,
  `parseBkgdData_accepts_grayAlpha8`,
  `parseBkgdData_accepts_grayAlpha16`,
  `parseBkgdData_accepts_gray16`,
  `parseBkgdData_accepts_rgb16`,
  `parseBkgdData_accepts_rgba16`,
  `parsePngLoopFuelWithMetadata_rejects_tRNS_after_idat`,
  `parsePngLoopFuelWithMetadata_rejects_bKGD_after_idat`,
  `parsePngLoopFuelWithMetadata_rejects_duplicate_tRNS`,
  `parsePngLoopFuelWithMetadata_rejects_duplicate_bKGD`,
  `parsePngLoopFuelWithMetadata_rejects_plte_after_metadata`,
  `parsePngLoopFuel_ignores_ancillary_before_idat`,
  `parsePngLoopFuel_idat_appends_when_open`);
- dynamic DEFLATE decoder correctness for proof-specified dynamic table reads,
  payload traces, dynamic-only multi-block streams, and zlib envelopes
  (`dynamicTableReaderSpec_readDynamicTables`, `dynamicPayloadTrace_decode_correct`,
  `dynamicDeflateStreamSpec_decode_correct`, `zlibDecompress_dynamicStreamSpec_correct`);
- row-filter reconstruction spec (RFC 2083 §6.2) with `unfilterRow_eq_spec`
  forward correctness against `reconstructRowSpec`, plus the multi-row chain
  `reconstructRowsSpec` (Phase 4 of the external-PNG plan);
- stored DEFLATE block forward correctness against an inductive
  `StoredDeflateStreamSpec` independent of the encoder
  (`storedBlockSpec_decode_correct`, `storedDeflateStreamSpec_decode_correct`,
  Phase 1a of the external-PNG plan);
- IHDR header round trip (`parseIHDRData_encodeIHDRData`) and container
  scaffolding (`SimpleContainerSpec`, `bytes_size`, `bytes_extract_signature`,
  `bytes_extract_skip_signature`, Phase 3a-3c-3d-partial);
- fixed-block forward-correctness scaffold: `FixedPayloadTransition`,
  `FixedPayloadFinish`, `FixedPayloadTrace`, and `FixedBlockSpec` inductive
  structures parallel to the dynamic spec (Phase 1b scaffold);
- there are no buffer overflows;
- PNG encode and decode are total functions.

## Proof Coverage Limits

The PNG round-trip proofs are encoder-to-decoder proofs for streams produced by this
library. They do not yet prove that the decoder accepts every valid PNG file or every
valid zlib/DEFLATE stream produced by another implementation. The exact 16-bit
bitmap round trips are proved; cross-depth 16-to-8 decoding is runtime-tested but
not yet exposed as a top-level theorem.

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

### External-PNG spec status

A multi-phase plan is in progress to extend the proof coverage to byte streams
*not* produced by this library's encoder. The phases that have landed:

- **Phase 4 (row filter)**: `Bitmap/Lemmas/Png/RowFilterSpec.lean` — complete.
- **Phase 1a (stored block)**: `Bitmap/Lemmas/Png/StoredBlockProofsSpec.lean` —
  complete, including the multi-block stream theorem.
- **Phase 3a-3d (PNG container)**: `Bitmap/Lemmas/Png/ContainerSpec.lean` — IHDR
  round trip + size/signature lemmas + signature-skip helper landed; the full
  `parsePng_simpleContainerSpec_correct` theorem (chunk-by-chunk byte arithmetic
  for IHDR/IDAT/IEND) is deferred.
- **Phase 1b (fixed block)**: `Bitmap/Lemmas/Png/FixedBlockProofsSpec.lean` —
  scaffold (inductive structures defined). The forward-correctness theorem is
  deferred and would mirror the dynamic spec's induction over the trace.
- **Phase 2 (mixed `BlockSpec` ADT) and Phase 5 (end-to-end composition)**: not
  yet started; depend on Phase 1b's final theorem.

## Supported PNG features

The encoder and decoder target a deliberately narrow PNG subset — the one for
which the library carries full round-trip correctness proofs.

### Encoder

| Area | Support |
|---|---|
| Color types | `0` Grayscale, `2` RGB, `4` Grayscale+Alpha, `6` RGBA |
| Bit depth | 8 or 16 bits per channel |
| Pixel formats | `PixelGray8`, `PixelRGB8`, `PixelGrayAlpha8`, `PixelRGBA8`, `PixelGray16`, `PixelRGB16`, `PixelGrayAlpha16`, `PixelRGBA16` |
| Filter type | `0` (None) only — every encoded row is written with filter byte `0x00` |
| Compression modes | `.stored` (uncompressed DEFLATE), `.fixed` (fixed-Huffman with LZ77 distance-1 run encoding), `.dynamic` (dynamic-block header; payload currently delegates to fixed-Huffman) |
| Interlace | None (no Adam7) |
| Chunks emitted | `IHDR`, one `IDAT`, `IEND` — no ancillary chunks |
| Integrity | CRC-32 per chunk, Adler-32 in the zlib trailer |
| Dimension limits | width and height each `< 2^32`, enforced by `encodeBitmapChecked` |

### Decoder

| Area | Support |
|---|---|
| Color types | `0`, `2`, `4`, `6` (palette `3` rejected) |
| Bit depth | 8 or 16 bits per channel |
| Filter types | All five reconstructed: `0` None, `1` Sub, `2` Up, `3` Average, `4` Paeth |
| Compression | `inflateStored` tried first, then fixed- and dynamic-Huffman zlib streams (full `HLIT`/`HDIST`/`HCLEN` + code-length-code + literal/length and distance tables) |
| LZ77 | Length codes 257–285 and distance codes 0–29 with extra bits; `copyDistance` supports overlap (distance < length) |
| Color conversion | RGB PNGs can be decoded into `BitmapRGBA8` (fills α = 255), gray+alpha PNGs into `BitmapRGBA8` (preserves alpha as expanded gray), and RGBA PNGs into `BitmapRGB8` (drops alpha). 16-bit PNGs may be decoded into matching 8-bit bitmap formats by taking the high byte of each sample |
| PNG structure | 8-byte signature, `IHDR` first, multiple consecutive `IDAT` chunks accepted and concatenated, `IEND` last, required `PLTE` ordering checks, rejects unknown critical chunks, compression/filter method ≠ 0, and interlace ≠ 0 |
| Tolerated ancillary chunks | `gAMA`, `cHRM`, `sRGB`, `iCCP`, `pHYs`, `tEXt`, `zTXt`, `iTXt`, `tIME`, `bKGD`, `hIST`, `sPLT`, plus any unknown chunk type whose first byte is lowercase — CRC-validated and skipped by the pixel-only decoder; supported `bKGD` is preserved and applied by metadata-aware decode |
| Metadata-aware decode | `decodeBitmapWithMetadata` validates and returns supported 8- and 16-bit `bKGD` metadata; it applies 8- and 16-bit grayscale/RGB `tRNS` transparency when decoding to RGBA, composites `tRNS` or RGBA alpha over `bKGD` when decoding to RGB, and composites grayscale+alpha over grayscale `bKGD` when decoding to RGB or grayscale. 16-bit sources can target exact 16-bit bitmaps or matching 8-bit bitmaps by high-byte downsampling after metadata handling |
| Integrity | CRC-32 verified for every parsed chunk; mismatch rejects the entire input. Adler-32 verified at end of zlib stream |

### Not supported

- Bit depths other than 8 and 16 (1, 2, 4)
- Color type 3 (palette / `PLTE`)
- Adam7 interlacing
- Palette `tRNS` and `bKGD` (requires color type 3 / `PLTE` decoding)
- `tRNS` through the pixel-only `decodeBitmap` API — use `decodeBitmapWithMetadata` for transparent-color decoding into `BitmapRGBA8`, or into `BitmapRGB8` when a valid `bKGD` background is present
- Gray+alpha through the pixel-only `decodeBitmap` API into non-alpha targets — use `decodeBitmapWithMetadata` for `BitmapRGB8` or `BitmapGray8` when a valid grayscale `bKGD` background is present
- `sBIT` chunks — explicitly **rejected** (decoder returns `none`) rather than silently ignored, to avoid the silent-corruption hazard of dropping precision metadata that affects pixel semantics
- Unknown critical chunks (any chunk type whose first byte is uppercase and not `IHDR`/`PLTE`/`IDAT`/`IEND`) — rejected per the PNG spec
- Reading-back of most ancillary chunk **content** (`gAMA`, `tEXt`, etc.) — the chunks are validated and skipped; `decodeBitmapWithMetadata` preserves supported `bKGD` and `tRNS`
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
