# bitmap

Lean 4 bitmap image utilities with verified PNG encode/decode support, plus a small widget for visualization.

Current library version: `0.9.0`.

The widget accepts the supported 8-bit bitmap formats and displays 16-bit bitmap
formats by downsampling each channel to its high byte for browser canvas output.
Packed 1-bit grayscale bitmaps are expanded to 8-bit grayscale for display, and
PNG `pHYs` metadata can drive physical-size or pixel-aspect rendering.

Proofs include functional correctness, guaranteed termination and no buffer overflows.

## Supported PNG features

The encoder and decoder target a deliberately narrow PNG subset — the one for
which the library implements directly. The byte-per-pixel bitmap formats in this
subset carry full round-trip correctness proofs; packed 1-bit grayscale and
explicit indexed-palette paths currently have focused layout, validation,
packed-row, raw decoder, parsed/container, exact indexed runtime-shape, and
checked-encoder filter-0 round-trip proofs for supported bit depths, plus
fixed/adaptive-filter, Adam7, multi-IDAT, palette-transparency/background, and
expansion runtime fixture coverage.

### Encoder

| Area | Support |
|---|---|
| Color types | `0` Grayscale, `2` RGB, `3` indexed-color palette, `4` Grayscale+Alpha, `6` RGBA |
| Bit depth | Grayscale: 1, 8, or 16 bits per channel. Indexed palette: 1, 2, 4, or 8 bits per index. RGB, Grayscale+Alpha, and RGBA: 8 or 16 bits per channel |
| Pixel formats | `PixelGray1`/`BitmapGray1`, `PixelGray8`, `PixelRGB8`, `PixelGrayAlpha8`, `PixelRGBA8`, `PixelGray16`, `PixelRGB16`, `PixelGrayAlpha16`, `PixelRGBA16`, plus explicit `PngIndexedBitmap` input for palette PNGs |
| Filter type | Existing `encodeBitmap` APIs emit filter `0` rows. `encodeBitmapWithOptionsChecked`, `encodeBitmapGray1WithOptionsChecked`, and `encodeIndexedBitmapWithOptionsChecked` can opt into fixed filters `0` None, `1` Sub, `2` Up, `3` Average, `4` Paeth, or deterministic adaptive per-row selection |
| Compression modes | `.stored` (uncompressed DEFLATE), `.fixed` (fixed-Huffman with greedy 32 KiB-window LZ77 encoding), `.dynamic` (generated dynamic-Huffman tables and dynamic-Huffman payload codes, using greedy 32 KiB-window LZ77 encoding) |
| Interlace | None (encoder always emits non-interlaced PNGs) |
| Chunks emitted | Existing pure `encodeBitmap` APIs emit `IHDR`, one `IDAT`, `IEND` only. `encodeBitmapWithOptionsChecked`, `encodeBitmapGray1WithOptionsChecked`, and `encodeIndexedBitmapWithOptionsChecked` can also emit validated `gAMA`, `cHRM`, `sRGB`, `pHYs`, or explicit `tIME` chunks, with optional compatible `gAMA=45455` before `sRGB` and compatible sRGB chromaticities before `sRGB`. The indexed encoder emits required `PLTE` plus optional palette `tRNS` and palette `bKGD` chunks. File-writing helpers emit the current UTC `tIME` by default; `writePngWithoutTime` keeps deterministic no-`tIME` output |
| Integrity | CRC-32 per chunk, Adler-32 in the zlib trailer |
| Dimension limits | width and height each `< 2^32`, enforced by checked bitmap and indexed encoder APIs |

### Decoder

| Area | Support |
|---|---|
| Color types | `0`, `2`, `3`, `4`, `6` |
| Bit depth | Grayscale: 1, 8, or 16 bits per channel. Indexed palette: 1, 2, 4, or 8 bits per index. RGB, Grayscale+Alpha, and RGBA: 8 or 16 bits per channel |
| Filter types | All five reconstructed: `0` None, `1` Sub, `2` Up, `3` Average, `4` Paeth |
| Interlace | None and Adam7 |
| Compression | `inflateStored` tried first, then fixed- and dynamic-Huffman zlib streams (full `HLIT`/`HDIST`/`HCLEN` + code-length-code + literal/length and distance tables) |
| LZ77 | Length codes 257–285 and distance codes 0–29 with extra bits; `copyDistance` supports overlap (distance < length) |
| Color conversion | 1-bit grayscale PNGs can be decoded into `BitmapGray1` exactly or expanded into 8-/16-bit grayscale, RGB, or RGBA targets using full-range black/white samples. Indexed palette PNGs can be decoded exactly with `decodeIndexedBitmap`/`decodeIndexedBitmapWithMetadata`, or expanded through `PLTE` into 8-/16-bit grayscale, RGB, grayscale+alpha, or RGBA targets; 16-bit targets use full-range `u8 * 257` channel expansion. RGB PNGs can be decoded into `BitmapRGBA8` (fills α = 255), gray+alpha PNGs into `BitmapRGBA8` (preserves alpha as expanded gray), and RGBA PNGs into `BitmapRGB8` (drops alpha). 16-bit PNGs may be decoded into matching 8-bit bitmap formats by taking the high byte of each sample |
| Color space | `sRGB` chunks are validated, preserved in metadata-aware decode, and treated as already-sRGB samples. `gAMA` chunks are validated and preserved. `cHRM` chunks are validated, preserved, and when no `sRGB` chunk is present, RGB/RGBA source samples are converted to sRGB using cHRM primaries plus `gAMA` when present, or linear-light source samples when `gAMA` is absent. Palette samples are expanded through `PLTE` before color-space conversion. `sRGB` with `gAMA` is accepted only for compatible `gAMA=45455`; `sRGB` with `cHRM` is accepted only for compatible sRGB chromaticities; `sRGB` takes precedence |
| Physical density | `pHYs` chunks are validated, preserved in metadata-aware decode, and exposed as exact pixels-per-unit values plus helper DPI conversion for metre-based density. The widget uses metre-based `pHYs` for CSS physical size and unknown-unit `pHYs` for pixel-aspect correction |
| PNG structure | 8-byte signature, `IHDR` first, multiple consecutive `IDAT` chunks accepted and concatenated, `IEND` last, required `PLTE` ordering checks, required valid `PLTE` before `IDAT` for palette PNGs, rejects unknown critical chunks, compression/filter method ≠ 0, and interlace methods other than `0` or `1` |
| Tolerated ancillary chunks | `iCCP`, `tEXt`, `zTXt`, `iTXt`, `hIST`, `sPLT`, plus any unknown chunk type whose first byte is lowercase — CRC-validated and skipped. Supported `gAMA`, `cHRM`, `sRGB`, `pHYs`, `tIME`, `bKGD`, and `tRNS` are validated by their dedicated parser branches |
| Metadata-aware decode | `decodeBitmapWithMetadata` validates and returns supported `gAMA`, `cHRM`, `sRGB`, `pHYs`, `tIME`, `PLTE`, 1-bit grayscale plus 8- and 16-bit grayscale/RGB/palette `bKGD` metadata; it applies supported grayscale/RGB/palette `tRNS` transparency when decoding to RGBA, composites `tRNS` or RGBA alpha over `bKGD` when decoding to RGB, and composites grayscale+alpha over grayscale `bKGD` when decoding to RGB or grayscale. Palette `tRNS` can be decoded into non-alpha targets only when a valid palette `bKGD` is present. 16-bit sources can target exact 16-bit bitmaps or matching 8-bit bitmaps by high-byte downsampling after metadata handling |
| Integrity | CRC-32 verified for every parsed chunk; mismatch rejects the entire input. Adler-32 verified at end of zlib stream |

### Not supported

- Non-palette 2- and 4-bit grayscale PNGs
- Truecolor RGB bit depth 1 (PNG forbids color type 2 at bit depth 1)
- Encoder-side Adam7 interlacing
- Automatic palette quantization from RGB/RGBA bitmap input — palette encoding requires explicit `PngIndexedBitmap` input
- `tRNS` through the pixel-only `decodeBitmap` API — use `decodeBitmapWithMetadata` for transparent-color decoding into `BitmapRGBA8`, or into `BitmapRGB8` when a valid `bKGD` background is present
- Gray+alpha through the pixel-only `decodeBitmap` API into non-alpha targets — use `decodeBitmapWithMetadata` for `BitmapRGB8` or `BitmapGray8` when a valid grayscale `bKGD` background is present
- `sBIT` chunks — explicitly **rejected** (decoder returns `none`) rather than silently ignored, to avoid the silent-corruption hazard of dropping precision metadata that affects pixel semantics
- Unknown critical chunks (any chunk type whose first byte is uppercase and not `IHDR`/`PLTE`/`IDAT`/`IEND`) — rejected per the PNG spec
- Reading-back of most ancillary chunk **content** (`tEXt`, `iCCP`, etc.) — those chunks are validated and skipped; `decodeBitmapWithMetadata` preserves supported `PLTE`, `gAMA`, `cHRM`, `sRGB`, `pHYs`, `tIME`, `bKGD`, and `tRNS`

## Usage

```lean
import Bitmap
```

## Tests

```sh
lake test
```

## Proofs

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
  `pngColorTypeBitDepthSupported_palette1`,
  `pngColorTypeBitDepthSupported_palette2`,
  `pngColorTypeBitDepthSupported_palette4`,
  `pngColorTypeBitDepthSupported_palette8`,
  `pngColorTypeBitDepthSupported_palette16_false`,
  `parsePlteData_accepts_palette2`,
  `parsePlteData_rejects_empty_palette`,
  `parsePlteData_rejects_bad_length`,
  `parsePlteData_rejects_palette_too_large_for_depth1`,
  `parsePngLoopFuelWithMetadata_accepts_PLTE`,
  `parseTrnsData_accepts_paletteAlpha`,
  `parsePngLoopFuelWithMetadata_accepts_palette_tRNS`,
  `parsePngLoopFuelWithMetadata_rejects_palette_tRNS_before_PLTE`,
  `parsePngLoopFuelWithMetadata_rejects_palette_tRNS_without_palette`,
  `parsePngLoopFuelWithMetadata_rejects_palette_tRNS_too_long`,
  `parseBkgdData_accepts_paletteIndex`,
  `parsePngLoopFuelWithMetadata_accepts_palette_bKGD`,
  `parsePngLoopFuelWithMetadata_rejects_palette_bKGD_before_PLTE`,
  `parsePngLoopFuelWithMetadata_rejects_palette_bKGD_without_palette`,
  `parsePngLoopFuelWithMetadata_rejects_palette_bKGD_index_out_of_range`,
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
- focused indexed-palette helper facts for PNG bit-depth validation, `PLTE`
  acceptance/rejection, palette `tRNS`/`bKGD` parsing, metadata chunk-order
  acceptance, checked encoder validation rejection paths, Boolean range
  validation from flat and coordinate-wise pixel bounds, symbolic packed-row
  round trips for all supported palette bit depths, smaller-palette raw decode
  when every source index is below the actual palette entry count, exact
  indexed runtime-shape round trips through parsed/container/public checked
  encoder layers, and public checked indexed encoder round-trip theorems for
  all palette bit depths whose checked range predicate is derived from the
  indexed bitmap shape
  (`pngColorTypeBitDepthSupported_palette1`,
  `pngColorTypeBitDepthSupported_palette2`,
  `pngColorTypeBitDepthSupported_palette4`,
  `pngColorTypeBitDepthSupported_palette8`,
  `paletteRowBytes_eq`,
  `paletteMaxEntriesForBitDepth_eq_paletteIndexLimit`,
  `pngRowBytes_palette1`,
  `pngRowBytes_palette2`,
  `pngRowBytes_palette4`,
  `pngRowBytes_palette8`,
  `paletteRowBytes_1`,
  `paletteRowBytes_2`,
  `paletteRowBytes_4`,
  `paletteRowBytes_8`,
  `paletteScatterFullRow_8_256`,
  `paletteScatterFullRow_succeeds_of_indexLimit`,
  `paletteScatterFullRow_succeeds_of_rowRange_nonfast`,
  `paletteScatterFullRow_get!_of_indexLimit_non8`,
  `paletteScatterFullRow_get!_of_rowRange_nonfast`,
  `paletteScatterFullRow_preserves_lt_rowStart_non8`,
  `paletteScatterFullRow_preserves_lt_rowStart_of_rowRange_nonfast`,
  `paletteScatterFullRow_size_of_some_non8`,
  `paletteScatterFullRow_size_of_some_nonfast`,
  `adam7ScatterRowPalette_empty_width`,
  `adam7ScatterRowPalette_succeeds_of_indexLimit`,
  `adam7ScatterRowPalette_get!_of_indexLimit`,
  `decodeAdam7PalettePassRows_empty_height`,
  `decodeAdam7PalettePasses_nil`,
  `palettePackedIndexAt_lt_indexLimit`,
  `palettePackedIndexAt_lt_entries`,
  `palettePackedIndexAt_pack_same`,
  `palettePackedIndexAt_pack_other`,
  `palettePackedByteIndex_lt_rowBytes`,
  `encodeIndexedPackedRowLoop_indices`,
  `encodeIndexedPackedRowLoop_zeroRow_indices`,
  `pushU16Full_eq_push_sample_twice`,
  `alphaCompositeByte_opaque`,
  `alphaCompositeByte_transparent`,
  `alphaCompositeByte_same`,
  `alphaCompositeByte_paletteAlphaAt_none`,
  `grayFromRGB8_uniform`,
  `pushU16Full_grayFromRGB8_uniform`,
  `paletteAlphaBytes?_paletteAlpha`,
  `paletteAlphaBytes?_none`,
  `paletteAlphaBytes?_non_palette`,
  `paletteAlphaAt_none`,
  `paletteAlphaAt_some_lt`,
  `paletteAlphaAt_some_ge`,
  `paletteBackgroundRGB?_paletteIndex`,
  `paletteBackgroundRGB?_none`,
  `paletteBackgroundRGB?_non_palette`,
  `paletteRgbAt?_of_base_lt`,
  `paletteRgbAt?_of_base_ge`,
  `paletteRgbAt?_of_lt_entryCount`,
  `paletteBackgroundRGB?_paletteIndex_of_lt_entryCount`,
  `expandPaletteIndicesToPixels8_unsupported_colorType`,
  `expandPaletteIndicesToPixels16_unsupported_colorType`,
  `expandPaletteIndicesToPixels8_empty_supported`,
  `expandPaletteIndicesToPixels16_empty_supported`,
  `expandPaletteIndicesToPixels_empty_supported`,
  `expandPaletteIndicesToPixels_unsupported_colorType`,
  `expandPaletteIndicesToPixels_unsupported_bitDepth`,
  `encodeIndexedPackedRows_size`,
  `encodeIndexedPackedRows_8_eq_data`,
  `encodeIndexedPackedRows_indices_non8`,
  `encodeRawIndexedWithFilter_size`,
  `encodeIndexedRowsWithFilter_none_eq_encodeRawGray8`,
  `decodePaletteRowsLoop_encodeIndexedRowsWithFilter_none_8_256`,
  `decodePaletteIndicesByInterlace_encodeIndexedRowsWithFilter_none_8_256`,
  `decodePaletteIndicesByInterlace_encodeIndexedRowsWithFilter_none_of_packed_indices_nonfast`,
  `decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_8_256`,
  `decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_8_paletteRange`,
  `decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8`,
  `decodePaletteIndicesByInterlace_encodeRawIndexedWithFilter_none_non8_paletteRange`,
  `decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_256_data`,
  `decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_paletteRange_data`,
  `decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_data`,
  `decodeParsedIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_paletteRange_data`,
  `decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_256_data`,
  `decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_paletteRange_data`,
  `decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_data`,
  `decodeParsedIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_paletteRange_data`,
  `decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_256_data`,
  `decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_paletteRange_data`,
  `decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_data`,
  `decodeParsedIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_paletteRange_data`,
  `indexedBitmapShape`,
  `indexedDecodeResultShape`,
  `decodeParsedIndexedBitmapWithMetadata_encodeRawIndexed_none_paletteRange_shape`,
  `PaletteContainerSpec.bytes_size`,
  `PaletteContainerSpec.parsePlteData`,
  `PaletteContainerSpec.readChunk_ihdr`,
  `PaletteContainerSpec.readChunk_plte`,
  `PaletteContainerSpec.readChunk_idat`,
  `PaletteContainerSpec.readChunk_iend`,
  `PaletteContainerSpec.parsePngLoopFuelWithMetadata_accepts_with_extra`,
  `PaletteContainerSpec.parsePngLoopFuelWithMetadata_accepts`,
  `PaletteContainerSpec.parsePngSimple_eq_none`,
  `PaletteContainerSpec.parsePngSimpleWithMetadata_eq_none`,
  `PaletteContainerSpec.parsePngWithMetadata_accepts`,
  `PaletteContainerSpec.parsePngForDecode_accepts`,
  `PaletteContainerSpec.decodeIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_non8_data`,
  `PaletteContainerSpec.decodeIndexedBitmapWithMetadata_stored_encodeRawIndexed_none_8_256_data`,
  `PaletteContainerSpec.decodeIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_non8_data`,
  `PaletteContainerSpec.decodeIndexedBitmapWithMetadata_fixed_encodeRawIndexed_none_8_256_data`,
  `PaletteContainerSpec.decodeIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_non8_data`,
  `PaletteContainerSpec.decodeIndexedBitmapWithMetadata_dynamic_encodeRawIndexed_none_8_256_data`,
  `PaletteContainerSpec.decodeIndexedBitmap_stored_encodeRawIndexed_none_non8_data`,
  `PaletteContainerSpec.decodeIndexedBitmap_stored_encodeRawIndexed_none_8_256_data`,
  `PaletteContainerSpec.decodeIndexedBitmap_fixed_encodeRawIndexed_none_non8_data`,
  `PaletteContainerSpec.decodeIndexedBitmap_fixed_encodeRawIndexed_none_8_256_data`,
  `PaletteContainerSpec.decodeIndexedBitmap_dynamic_encodeRawIndexed_none_non8_data`,
  `PaletteContainerSpec.decodeIndexedBitmap_dynamic_encodeRawIndexed_none_8_256_data`,
  `PaletteContainerSpec.decodeIndexedBitmapWithMetadata_encodeRawIndexed_none_paletteRange_data`,
  `PaletteContainerSpec.decodeIndexedBitmap_encodeRawIndexed_none_paletteRange_data`,
  `PaletteContainerSpec.decodeIndexedBitmapWithMetadata_encodeRawIndexed_none_paletteRange_shape`,
  `PaletteContainerSpec.decodeIndexedBitmap_encodeRawIndexed_none_paletteRange_shape`,
  `ExternalIndexedPalettePngSpec.decodeIndexedBitmapWithMetadata_external_correct`,
  `ExternalIndexedPalettePngSpec.decodeIndexedBitmap_external_correct`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_8_256_data`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_stored_8_256_data`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_fixed_8_256_data`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_dynamic_8_256_data`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_non8_data`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_stored_non8_data`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_fixed_non8_data`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_dynamic_non8_data`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_supported_bitDepth_data`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_paletteRange_data`,
  `PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_paletteRange_shape`,
  `PalettePackedRoundTrip.checked_roundtrip_fixture_for_supported_bitDepth`,
  `PalettePackedRoundTrip.checked_fixed_filter_roundtrip_fixture_for_supported_bitDepth`,
  `PalettePackedRoundTrip.checked_fixed_filter_shape_fixture_for_supported_bitDepth`,
  `PalettePackedRoundTrip.checked_adaptive_filter_shape_fixture_for_supported_bitDepth`,
  `PalettePackedRoundTrip.checked_palette_expansion_fixture_for_supported_bitDepth`,
  `PalettePackedRoundTrip.checked_stored_1bit_fixture_data`,
  `PalettePackedRoundTrip.checked_fixed_1bit_fixture_data`,
  `PalettePackedRoundTrip.checked_dynamic_1bit_fixture_data`,
  `PalettePackedRoundTrip.checked_stored_2bit_fixture_data`,
  `PalettePackedRoundTrip.checked_fixed_2bit_fixture_data`,
  `PalettePackedRoundTrip.checked_dynamic_2bit_fixture_data`,
  `PalettePackedRoundTrip.checked_stored_4bit_fixture_data`,
  `PalettePackedRoundTrip.checked_fixed_4bit_fixture_data`,
  `PalettePackedRoundTrip.checked_dynamic_4bit_fixture_data`,
  `PalettePackedRoundTrip.checked_stored_8bit_fixture_data`,
  `PalettePackedRoundTrip.checked_fixed_8bit_fixture_data`,
  `PalettePackedRoundTrip.checked_dynamic_8bit_fixture_data`,
  `PalettePackedRoundTrip.decodeIndexedBitmap_adam7_fixture_for_supported_bitDepth`,
  `PalettePackedRoundTrip.decodeIndexedBitmapWithMetadata_adam7_fixture_for_supported_bitDepth_shape`,
  `PalettePackedRoundTrip.decodeIndexedBitmap_adam7_2bit_fixture`,
  `PalettePackedRoundTrip.decodeIndexedBitmap_multiIDAT_4bit_fixture`,
  `PalettePackedRoundTrip.decodeIndexedBitmapWithMetadata_multiIDAT_4bit_fixture_shape`,
  `PalettePackedRoundTrip.decodeBitmapWithMetadata_palette_tRNS_RGBA8_fixture`,
  `PalettePackedRoundTrip.decodeBitmapWithMetadata_palette_tRNS_bKGD_RGB8_fixture`,
  `PalettePackedRoundTrip.decodeBitmap_palette_tRNS_pixelOnly_rejects_RGBA8_fixture`,
  `PalettePackedRoundTrip.decodeIndexedBitmapWithMetadata_palette_tRNS_bKGD_fixture`,
  `PalettePackedRoundTrip.decodeIndexedBitmapWithMetadata_palette_metadata_fixture`,
  `PalettePackedRoundTrip.decodeIndexedBitmapWithMetadata_palette_tRNS_bKGD_shape_fixture`,
  `PalettePackedRoundTrip.decodeBitmap_palette_RGB16_fixture`,
  `PalettePackedRoundTrip.decodeBitmap_palette_RGBA16_fixture`,
  `PalettePackedRoundTrip.decodeBitmap_palette_Gray16_fixture`,
  `PalettePackedRoundTrip.decodeBitmap_palette_GrayAlpha16_fixture`,
  `PalettePackedRoundTrip.decodeBitmapWithMetadata_palette_gAMA_RGB8_fixture`,
  `PalettePackedRoundTrip.decodeBitmapWithMetadata_palette_sRGB_RGB8_fixture`,
  `PalettePackedRoundTrip.decodeBitmapWithMetadata_palette_sRGB_metadata_fixture`,
  `PalettePackedRoundTrip.decodeBitmapWithMetadata_palette_cHRM_gAMA_RGB8_fixture`,
  `PalettePackedRoundTrip.decodeBitmapWithMetadata_palette_cHRM_gAMA_metadata_fixture`,
  `PaletteValidation.validateIndexedBitmap_accepts`,
  `PaletteValidation.validateIndexedBitmap_accepts_of_paletteIndexLimit`,
  `PaletteValidation.indexedDataInRange_true_of_forall_get!`,
  `PaletteValidation.indexedDataInRange_true_of_valid_coordinates`,
  `PaletteValidation.encodeIndexedBitmapWithOptionsChecked_rejects_of_validate_error`,
  `PaletteValidation.validateIndexedBitmap_rejects_bad_bitDepth`,
  `PaletteValidation.validateIndexedBitmap_rejects_width_limit`,
  `PaletteValidation.validateIndexedBitmap_rejects_height_limit`,
  `PaletteValidation.validateIndexedBitmap_rejects_empty_palette`,
  `PaletteValidation.validateIndexedBitmap_rejects_bad_palette_length`,
  `PaletteValidation.validateIndexedBitmap_rejects_palette_oversize`,
  `PaletteValidation.validateIndexedBitmap_rejects_palette_too_large_for_depth1`,
  `PaletteValidation.validateIndexedBitmap_rejects_out_of_range_indices`,
  `PaletteValidation.validateIndexedBitmap_rejects_alpha_too_long`,
  `PaletteValidation.validateIndexedBitmap_rejects_background_out_of_range`,
  `parsePlteData_accepts_palette2`,
  `parsePlteData_accepts_valid`,
  `parseTrnsData_accepts_paletteAlpha`,
  `parseBkgdData_accepts_paletteIndex`);
- focused encoder-filter helper facts for valid filter bytes, filter row size
  preservation, fixed-filter option sizing, adaptive filter-byte validity, and
  default filter-0 raw compatibility (`pngRowFilter_toByte_valid`,
  `filterRow_size`, `filterRowForStrategy_fixed_size`,
  `filterRowForStrategy_size`,
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
- end-to-end external-PNG correctness: any byte stream matching an
  `ExternalPngSpec` (8-bit depth, color types 0/2/4/6, non-interlaced,
  no ancillary chunks, no metadata, source matching target pixel type)
  is accepted by `decodeBitmap` and decodes to the spec's bitmap
  (`decodeBitmap_external_correct`, Phase 5 of the external-PNG plan);
- end-to-end multi-IDAT correctness: the same end-to-end guarantee
  generalised to byte streams with any positive number of `IDAT` chunks
  (`decodeBitmap_external_multiIdat_correct`, Phase 6 of the
  external-PNG plan);
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
public generated dynamic encoder is proved end-to-end through the runtime
`readDynamicTables` and generic dynamic payload decoder path; the older
fixed-shaped dynamic helper remains regression coverage.

The full-LZ77 encoder proof is a round-trip correctness proof for the streams
the encoder emits: every emitted match is valid, and decoding the generated
fixed or dynamic DEFLATE payload reconstructs the original bytes. The public
fixed and dynamic zlib wrappers are now proved through the greedy LZ77 encoder
paths (`zlibDecompress_zlibCompressFixed`, `zlibDecompress_zlibCompressDynamic`).
This does not prove that the greedy matcher chooses the globally smallest
compressed representation. Future compression-ratio work can add lazy matching,
which looks one byte ahead before committing to a match, and optimal parsing,
which chooses a lowest-cost literal/match sequence for the whole stream.

This is still not a standalone RFC-1951 grammar/completeness theorem independent of
the runtime parser, nor a single mixed stored/fixed/dynamic block-stream theorem.
The proof-level dynamic table boundary delegates bit-level header parsing to
`readDynamicTables`; runtime tests cover code-length repeats `16`, `17`, and `18`,
repeat overflow shape, literal-only zero-distance blocks, LZ77 matches, and dynamic
multi-block fixtures.

### LZ77 encoder proof status

The current greedy LZ77 proof path includes:

- `deflateTokensExpandLz77_deflateTokensLz77`: expanding the emitted token
  stream reconstructs the raw input.
- `zlibDecompress_zlibCompressFixed`: public fixed-Huffman zlib output decodes
  to the original raw bytes through the LZ77 token path.
- `zlibDecompress_zlibCompressDynamic`: public generated dynamic-Huffman zlib
  output decodes to the original raw bytes through the LZ77 token path.
- Generated dynamic LZ77 header and payload bridge lemmas, including
  `readDynamicTables_generatedDynamicLz77Suffix_readerAt_writeBits`,
  `decodeCompressedBlock_deflateTokensLz77Payload_suffix_readerAt_writeBits`,
  and `zlibDecompressLoop_deflateDynamicLz77`.

Good next theorem targets for stronger LZ77 specifications:

- `deflateDistanceInfo_decodeDistance_correct`: encoded distance symbol and
  extra bits decode back to the original distance.
- `deflateLengthInfo_decodeLength_correct`: encoded length symbol and extra
  bits decode back to the original match length.
- `copyDistance_spec`: arbitrary valid `distance` and `len` copy exactly the
  bytes described by the LZ77 back-reference, including overlap.
- `deflateTokensLz77_valid`: every emitted match has `3 ≤ len ≤ 258`,
  `1 ≤ distance ≤ 32768`, and `distance ≤ current output size`.
- `writeFixedPayload_lz77_decode_correct`: fixed-Huffman payload written from
  valid LZ77 tokens decodes to token expansion.
- `writeDynamicPayload_lz77_decode_correct`: generated dynamic-Huffman payload
  written from valid LZ77 tokens decodes to token expansion.

Future optional theorem targets:

- `lz77Greedy_longest_at_position`: the greedy finder chooses the longest match
  available at the current position.
- `lz77Greedy_tieBreaks_nearest`: equal-length matches choose the smallest
  distance.
- `lazyMatching_preserves_roundTrip`: lazy matching changes token choice but
  still expands to the same input.
- `optimalParsing_minimal_cost`: optimal parsing produces a token stream whose
  encoded bit cost is minimal under a fixed cost model.

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
  complete. `ExternalPngSpec` is a decoder-side spec with witnesses
  for each layer (container / zlib / row-filter + pixel extraction).
  The end-to-end theorem `decodeBitmap_external_correct` proves that
  any byte stream matching the spec is accepted by `decodeBitmap`
  and decodes to the spec's bitmap. Supported subset: 8-bit depth,
  color types 0/2/4/6, non-interlaced, no ancillary chunks, empty
  metadata, source color type matching target pixel type.
- **Phase 6 (multi-IDAT container)**:
  `Bitmap/Lemmas/Png/MultiIdatContainerSpec.lean` —
  complete. `MultiIdatContainerSpec` generalises `SimpleContainerSpec`
  to a non-empty list of `IDAT` chunk payloads (PNG spec compliance);
  `parsePng_multiIdatContainerSpec_correct` and
  `parsePngForDecode_multiIdatContainerSpec_correct` prove the
  basic-loop and metadata-aware parsers accept any matching byte
  stream. `Bitmap/Lemmas/MultiIdatExternalPngSpec.lean` lifts Phase 5
  to `ExternalPngMultiIdatSpec` /
  `decodeBitmap_external_multiIdat_correct`, threading the
  multi-chunk container through the unchanged zlib + row-filter
  witnesses (they consume the concatenated `container.idatData`).
