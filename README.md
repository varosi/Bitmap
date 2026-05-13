# bitmap

Lean 4 bitmap image utilities with PNG encode/decode support, plus a small widget for visualization.
The widget accepts the supported 8-bit bitmap formats and displays 16-bit bitmap
formats by downsampling each channel to its high byte for browser canvas output.
Packed 1-bit grayscale bitmaps are expanded to 8-bit grayscale for display, and
PNG `pHYs` metadata can drive physical-size or pixel-aspect rendering.

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
  `parseGammaData_accepts_45455`,
  `parseGammaData_rejects_zero`,
  `parseGammaData_rejects_bad_length`,
  `parseSrgbData_accepts_intents`,
  `parseSrgbData_rejects_bad_intent`,
  `parseChrmData_accepts_signed_values`,
  `parseChrmData_rejects_bad_length`,
  `encodeChrmData?_valid_size`,
  `encodeChrmData?_rejects_out_of_range`,
  `parsePngLoopFuelWithMetadata_accepts_gAMA`,
  `parsePngLoopFuelWithMetadata_accepts_cHRM`,
  `parsePngLoopFuelWithMetadata_accepts_sRGB`,
  `parsePngLoopFuelWithMetadata_rejects_gAMA_after_plte_or_idat`,
  `parsePngLoopFuelWithMetadata_rejects_cHRM_after_plte_or_idat`,
  `parsePngLoopFuelWithMetadata_rejects_sRGB_after_plte_or_idat`,
  `parsePngLoopFuelWithMetadata_rejects_duplicate_gAMA`,
  `parsePngLoopFuelWithMetadata_rejects_duplicate_cHRM`,
  `parsePngLoopFuelWithMetadata_rejects_duplicate_sRGB`,
  `parsePngLoopFuelWithMetadata_rejects_cHRM_after_incompatible_sRGB`,
  `parsePngLoopFuelWithMetadata_rejects_sRGB_after_incompatible_gAMA`,
  `parsePngLoopFuelWithMetadata_rejects_sRGB_after_incompatible_cHRM`,
  `parseTimeData_accepts_valid_time`,
  `parseTimeData_rejects_bad_length`,
  `parseTimeData_rejects_bad_month`,
  `parseTimeData_rejects_bad_day`,
  `encodeTimeData?_valid_size`,
  `parsePngLoopFuelWithMetadata_accepts_tIME`,
  `parsePngLoopFuelWithMetadata_rejects_duplicate_tIME`,
  `parsePhysData_accepts_meter_300dpi`,
  `parsePhysData_rejects_bad_length`,
  `parsePhysData_rejects_bad_unit`,
  `encodePhysData?_valid_size`,
  `dpiToPixelsPerMeterRounded_300`,
  `pixelsPerMeterToDpiRounded_11811`,
  `parsePngLoopFuelWithMetadata_accepts_pHYs`,
  `parsePngLoopFuelWithMetadata_rejects_pHYs_after_idat`,
  `parsePngLoopFuelWithMetadata_rejects_duplicate_pHYs`,
  `applyPngColorSpaceTransform_no_metadata`,
  `applyPngColorSpaceTransform_sRGB_noop`,
  `applyChrm8ToPixels_preserves_size`,
  `applyChrm8ToPixels_preserves_rgba_alpha_sample`,
  `applyGamma8ToPixels_preserves_rgba_alpha_sample`,
  `applyGamma16ToPixels_preserves_grayAlpha_alpha_sample`,
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
- focused Adam7 helper facts for pass geometry and filter-0 normalization size
  (`adam7PassCoord_lt_full`, `adam7FlatToFilterZeroRaw_size`);
- focused 1-bit grayscale helper facts for packed row geometry, PNG bit-depth
  validation, filter-0 raw size, and encoder raw size
  (`pngColorTypeBitDepthSupported_gray1`,
  `pngColorTypeBitDepthSupported_rgb1_false`, `gray1FlatToFilterZeroRaw_size`,
  `encodeRawGray1_size`);
- focused encoder-filter helper facts for valid filter bytes, filter row size
  preservation, fixed-filter option sizing, adaptive filter-byte validity, and
  default filter-0 raw compatibility (`pngRowFilter_toByte_valid`,
  `filterRow_size`, `filterRowForStrategy_fixed_size`,
  `adaptiveFilterRow_toByte_valid`, `encodeRawWithFilter_none_size`);
- stored DEFLATE block forward correctness against an inductive
  `StoredDeflateStreamSpec` independent of the encoder
  (`storedBlockSpec_decode_correct`, `storedDeflateStreamSpec_decode_correct`,
  Phase 1a of the external-PNG plan);
- IHDR header round trip (`parseIHDRData_encodeIHDRData`) and container
  scaffolding (`SimpleContainerSpec`, `bytes_size`, `bytes_extract_signature`,
  `bytes_extract_skip_signature`, Phase 3a-3c-3d-partial);
- fixed-block forward-correctness scaffold: `FixedPayloadTransition`,
  `FixedPayloadFinish`, `FixedPayloadTrace`, and `FixedBlockSpec` inductive
  structures parallel to the dynamic spec, plus the slow-variant
  forward-correctness theorem `fixedBlockSpec_decode_correct` (Phase 1b);
- fixed-block fast/slow decoder bridge: the runtime's fast
  `decodeFixedBlockFuelFast` is extensionally equivalent to the slow
  `decodeFixedBlockFuel` (`decodeFixedLiteralSymFast9_eq_decodeFixedLiteralSym`,
  `decodeFixedBlockFuelFast_eq_decodeFixedBlockFuel`,
  `fixedBlockSpec_decode_correct_fast`);
- mixed DEFLATE-stream forward correctness against an inductive
  `DeflateStreamSpec` covering stored, fixed, and dynamic blocks chained
  through `BFINAL` (`deflateStreamSpec_decodeFuel_correct`,
  `deflateStreamSpec_decode_correct`, Phase 2 of the external-PNG plan);
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
- **Phase 3a-3d (PNG container)**: `Bitmap/Lemmas/Png/ContainerSpec.lean` —
  complete, including `parsePng_simpleContainerSpec_correct`.
- **Phase 1b (fixed block)**: `Bitmap/Lemmas/Png/FixedBlockProofsSpec.lean` —
  complete (`fixedBlockSpec_decode_correct`). The runtime's fast variant
  is bridged in `Bitmap/Lemmas/Png/FixedBlockFastSlowBridge.lean` with
  `decodeFixedBlockFuelFast_eq_decodeFixedBlockFuel` and
  `fixedBlockSpec_decode_correct_fast`.
- **Phase 2 (mixed `BlockSpec` ADT + stream correctness)**:
  `Bitmap/Lemmas/Png/DeflateStreamSpec.lean` defines the
  `StoredBlockBitSpec`, `BlockSpec` (3-way sum), and `DeflateStreamSpec`
  inductive structures. `Bitmap/Lemmas/Png/DeflateStreamProofs.lean`
  proves `deflateStreamSpec_decode_correct` — any well-formed
  `DeflateStreamSpec` is accepted by the runtime
  `zlibDecompressLoop`, via per-block-type step lemmas (stored /
  fixed / dynamic) composed by induction.
- **Phase 5 (end-to-end composition)**: `Bitmap/Lemmas/ExternalPngSpec.lean` —
  scaffold (`ExternalPngSpec` structure). With Phases 1a/1b/2/3/4
  complete, the final theorem `decodeBitmap_external_correct` reduces
  to a routing exercise.

## Supported PNG features

The encoder and decoder target a deliberately narrow PNG subset — the one for
which the library implements directly. The byte-per-pixel bitmap formats in this
subset carry full round-trip correctness proofs; packed 1-bit grayscale currently
has focused layout and validation lemmas plus runtime fixture coverage.

### Encoder

| Area | Support |
|---|---|
| Color types | `0` Grayscale, `2` RGB, `4` Grayscale+Alpha, `6` RGBA |
| Bit depth | Grayscale: 1, 8, or 16 bits per channel. RGB, Grayscale+Alpha, and RGBA: 8 or 16 bits per channel |
| Pixel formats | `PixelGray1`/`BitmapGray1`, `PixelGray8`, `PixelRGB8`, `PixelGrayAlpha8`, `PixelRGBA8`, `PixelGray16`, `PixelRGB16`, `PixelGrayAlpha16`, `PixelRGBA16` |
| Filter type | Existing `encodeBitmap` APIs emit filter `0` rows. `encodeBitmapWithOptionsChecked` and `encodeBitmapGray1WithOptionsChecked` can opt into fixed filters `0` None, `1` Sub, `2` Up, `3` Average, `4` Paeth, or deterministic adaptive per-row selection |
| Compression modes | `.stored` (uncompressed DEFLATE), `.fixed` (fixed-Huffman with LZ77 distance-1 run encoding), `.dynamic` (dynamic-block header; payload currently delegates to fixed-Huffman) |
| Interlace | None (encoder always emits non-interlaced PNGs) |
| Chunks emitted | Existing pure `encodeBitmap` APIs emit `IHDR`, one `IDAT`, `IEND` only. `encodeBitmapWithOptionsChecked` and `encodeBitmapGray1WithOptionsChecked` can also emit validated `gAMA`, `cHRM`, `sRGB`, `pHYs`, or explicit `tIME` chunks, with optional compatible `gAMA=45455` before `sRGB` and compatible sRGB chromaticities before `sRGB`. File-writing helpers emit the current UTC `tIME` by default; `writePngWithoutTime` keeps deterministic no-`tIME` output |
| Integrity | CRC-32 per chunk, Adler-32 in the zlib trailer |
| Dimension limits | width and height each `< 2^32`, enforced by `encodeBitmapChecked` |

### Decoder

| Area | Support |
|---|---|
| Color types | `0`, `2`, `4`, `6` (palette `3` rejected) |
| Bit depth | Grayscale: 1, 8, or 16 bits per channel. RGB, Grayscale+Alpha, and RGBA: 8 or 16 bits per channel |
| Filter types | All five reconstructed: `0` None, `1` Sub, `2` Up, `3` Average, `4` Paeth |
| Interlace | None and Adam7 |
| Compression | `inflateStored` tried first, then fixed- and dynamic-Huffman zlib streams (full `HLIT`/`HDIST`/`HCLEN` + code-length-code + literal/length and distance tables) |
| LZ77 | Length codes 257–285 and distance codes 0–29 with extra bits; `copyDistance` supports overlap (distance < length) |
| Color conversion | 1-bit grayscale PNGs can be decoded into `BitmapGray1` exactly or expanded into 8-/16-bit grayscale, RGB, or RGBA targets using full-range black/white samples. RGB PNGs can be decoded into `BitmapRGBA8` (fills α = 255), gray+alpha PNGs into `BitmapRGBA8` (preserves alpha as expanded gray), and RGBA PNGs into `BitmapRGB8` (drops alpha). 16-bit PNGs may be decoded into matching 8-bit bitmap formats by taking the high byte of each sample |
| Color space | `sRGB` chunks are validated, preserved in metadata-aware decode, and treated as already-sRGB samples. `gAMA` chunks are validated and preserved. `cHRM` chunks are validated, preserved, and when no `sRGB` chunk is present, RGB/RGBA source samples are converted to sRGB using cHRM primaries plus `gAMA` when present, or linear-light source samples when `gAMA` is absent. `sRGB` with `gAMA` is accepted only for compatible `gAMA=45455`; `sRGB` with `cHRM` is accepted only for compatible sRGB chromaticities; `sRGB` takes precedence |
| Physical density | `pHYs` chunks are validated, preserved in metadata-aware decode, and exposed as exact pixels-per-unit values plus helper DPI conversion for metre-based density. The widget uses metre-based `pHYs` for CSS physical size and unknown-unit `pHYs` for pixel-aspect correction |
| PNG structure | 8-byte signature, `IHDR` first, multiple consecutive `IDAT` chunks accepted and concatenated, `IEND` last, required `PLTE` ordering checks, rejects unknown critical chunks, compression/filter method ≠ 0, and interlace methods other than `0` or `1` |
| Tolerated ancillary chunks | `iCCP`, `tEXt`, `zTXt`, `iTXt`, `hIST`, `sPLT`, plus any unknown chunk type whose first byte is lowercase — CRC-validated and skipped. Supported `gAMA`, `cHRM`, `sRGB`, `pHYs`, `tIME`, `bKGD`, and `tRNS` are validated by their dedicated parser branches |
| Metadata-aware decode | `decodeBitmapWithMetadata` validates and returns supported `gAMA`, `cHRM`, `sRGB`, `pHYs`, `tIME`, 1-bit grayscale plus 8- and 16-bit grayscale/RGB `bKGD` metadata; it applies supported grayscale/RGB `tRNS` transparency when decoding to RGBA, composites `tRNS` or RGBA alpha over `bKGD` when decoding to RGB, and composites grayscale+alpha over grayscale `bKGD` when decoding to RGB or grayscale. 16-bit sources can target exact 16-bit bitmaps or matching 8-bit bitmaps by high-byte downsampling after metadata handling |
| Integrity | CRC-32 verified for every parsed chunk; mismatch rejects the entire input. Adler-32 verified at end of zlib stream |

### Not supported

- Bit depths 2 and 4
- Truecolor RGB bit depth 1 (PNG forbids color type 2 at bit depth 1)
- Color type 3 (palette / `PLTE`)
- Encoder-side Adam7 interlacing
- Palette `tRNS` and `bKGD` (requires color type 3 / `PLTE` decoding)
- `tRNS` through the pixel-only `decodeBitmap` API — use `decodeBitmapWithMetadata` for transparent-color decoding into `BitmapRGBA8`, or into `BitmapRGB8` when a valid `bKGD` background is present
- Gray+alpha through the pixel-only `decodeBitmap` API into non-alpha targets — use `decodeBitmapWithMetadata` for `BitmapRGB8` or `BitmapGray8` when a valid grayscale `bKGD` background is present
- `sBIT` chunks — explicitly **rejected** (decoder returns `none`) rather than silently ignored, to avoid the silent-corruption hazard of dropping precision metadata that affects pixel semantics
- Unknown critical chunks (any chunk type whose first byte is uppercase and not `IHDR`/`PLTE`/`IDAT`/`IEND`) — rejected per the PNG spec
- Reading-back of most ancillary chunk **content** (`tEXt`, `iCCP`, etc.) — those chunks are validated and skipped; `decodeBitmapWithMetadata` preserves supported `gAMA`, `cHRM`, `sRGB`, `pHYs`, `tIME`, `bKGD`, and `tRNS`
- Genuinely-distinct dynamic-Huffman encoding — `.dynamic` emits a dynamic-block header but delegates the deflate payload to fixed-Huffman

## Usage

```lean
import Bitmap
```

## Tests

```sh
lake test
```
