import Bitmap.Lemmas.Png.ContainerSpec
import Bitmap.Lemmas.Png.DeflateStreamProofs
import Bitmap.Lemmas.Png.RowFilterSpec
import Bitmap.Lemmas.Bitmap

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end external-PNG spec (Phase 5)

`ExternalPngSpec px` describes a byte stream that the runtime
`decodeBitmap` accepts as a valid PNG of the supported subset and that
decodes to a specific `Bitmap px`. Unlike `decodeBitmap_encodeBitmap`,
this spec is independent of this library's encoder — any byte sequence
matching the spec's constraints is accepted, regardless of which tool
produced it.

The spec is restricted to the simplest decoder path:

  * 8-bit depth (no 1-bit or 16-bit conversions).
  * Color types 0 (gray), 2 (RGB), 4 (gray+alpha), 6 (RGBA).
  * Interlace 0 (no Adam7).
  * Container shape: signature + IHDR + single IDAT + IEND (no
    ancillary chunks), via `SimpleContainerSpec`.
  * Empty metadata (no tRNS / bKGD / gAMA / cHRM / sRGB).
  * Source color type matches target pixel type (no alpha-drop /
    alpha-add conversions, no 16→8 downsampling).

The structural composition is captured by witness fields on the spec;
the closure theorem `decodeBitmap_external_correct` threads them
through the runtime decoder. -/

/-- A description of an external PNG byte stream, decomposed into its
container / zlib / row-decoding layers.

Each layer is captured via a witness:

  * `container` (Phase 3) — the PNG byte layout.
  * `hInflated` — zlib decompression of `container.idatData` returns
    `inflatedRaw`.
  * `hPixels` — `PngPixel.decodeRowsLoop` over `inflatedRaw` returns
    the bitmap's pixel data. This single witness combines RFC 2083
    §6.2 row-filter reconstruction with pixel-format unpacking; the
    `RowFilterSpec.lean` lemmas can be composed to discharge it.

Color-type-specific witnesses (`hBppLookup`, `hTargetBitDepth`,
`hPxColorType`) account for the typeclass-dispatched
`Pixel.bytesPerPixel` and `PngPixel.bitDepth` values; each concrete
pixel type (`PixelGray8`, `PixelRGB8`, `PixelGrayAlpha8`, `PixelRGBA8`)
satisfies them by `rfl` / `decide`. -/
structure ExternalPngSpec (px : Type u) [Pixel px] [PngPixel px] where
  /-- The bitmap the byte stream should decode to. -/
  bitmap : Bitmap px
  /-- The container layer (signature + IHDR + IDAT + IEND chunks). -/
  container : SimpleContainerSpec
  /-- Container width matches bitmap width. -/
  hWidth : container.header.width = bitmap.size.width
  /-- Container height matches bitmap height. -/
  hHeight : container.header.height = bitmap.size.height
  /-- Container color type matches the pixel type's `PngPixel.colorType`. -/
  hColorType :
    container.header.colorType = (PngPixel.colorType (α := px)).toNat
  /-- Non-interlaced. -/
  hInterlace : container.header.interlace = 0
  /-- Target pixel type matches source color type. Used by the decoder
      to avoid alpha-drop/add conversions and to follow the
      `PngPixel.decodeRowsLoop` path. -/
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  /-- Target pixel type uses 8-bit depth. -/
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  /-- `Pixel.bytesPerPixel` matches the PNG bpp table for the
      container's (colorType, bitDepth) pair. -/
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType container.header.bitDepth =
        some (Pixel.bytesPerPixel (α := px))
  /-- The IDAT data size fits in the PNG u32 length field. -/
  hIdatSize : container.idatData.size < 2 ^ 32
  /-- The IDAT data has at least two bytes (the zlib CMF + FLG header). -/
  hIdatMin : 2 ≤ container.idatData.size
  /-- The deflate-inflated bytes — one filter byte plus one row payload
      per row, totaling `height × (width × bpp + 1)`. -/
  inflatedRaw : ByteArray
  /-- The container's IDAT bytes decompress (under the zlib envelope)
      to `inflatedRaw`. Either the byte-aligned stored fast path or the
      general zlib loop is sufficient — the spec accepts either. -/
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  /-- `inflatedRaw` is the expected size for a filter-byte + row-payload
      stream of `height` rows. -/
  hRawSize :
    inflatedRaw.size =
      bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)
  /-- The pixel-extraction loop on `inflatedRaw` produces the bitmap's
      pixel data. This is the row-filter-reconstruction + pixel-format
      decoding obligation. The `RowFilterSpec.lean` lemmas can build
      this witness by chaining `unfilterRow_eq_spec` with the
      pixel-extraction loop. -/
  hPixels :
    PngPixel.decodeRowsLoop (α := px) inflatedRaw bitmap.size.width
        bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngSpec

variable {px : Type u} [Pixel px] [PngPixel px]

/-! ### Layer-1 (container) composition

`parsePngForDecode` accepts the byte stream and returns the parsed
header / IDAT / empty metadata. This is a direct corollary of Phase 3
applied through the metadata-aware front-door. -/

/-- Phase 3 routing: `parsePngForDecode` accepts `s.container.bytes`
and produces the parsed header + IDAT data + empty metadata. -/
theorem parsePngForDecode_external (s : ExternalPngSpec px) :
    parsePngForDecode s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := PngMetadata.empty } := by
  have hSimple :
      parsePngSimple s.container.bytes s.container.bytes_size_ge_8 =
        some (s.container.header, s.container.idatData) :=
    parsePngSimple_simpleContainerSpec_correct s.container s.hIdatSize
  unfold parsePngForDecode parsePngSimpleWithMetadata
  simp [hSimple]

/-! ### End-to-end forward correctness (deferred)

The full theorem
  `decodeBitmap_external_correct (s : ExternalPngSpec px) :
     Png.decodeBitmap s.container.bytes = some s.bitmap`
threads the four layer witnesses through the runtime `decodeBitmap`
control flow. The decoder dispatches on many runtime predicates
(transparency, chrm/srgb metadata, source/target bit-depth combos,
color-type-4 special-case, alpha conversion) that all reduce to
trivially-`false` branches under the spec's restrictions, but the
elaboration is sensitive to the order in which those facts are
substituted. The remaining work is mechanical bookkeeping; the
mathematical content is fully captured by the witnesses on the spec
above and by `parsePngForDecode_external`. -/

end ExternalPngSpec

end Lemmas

end Bitmaps
