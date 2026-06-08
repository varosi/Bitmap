import Bitmap.Lemmas.MultiIdatExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore
import Bitmap.Lemmas.Png.MultiIdatTrnsContainerSpec

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end multi-IDAT + tRNS forward-decode spec (RGBA8 target)

`ExternalPngMultiIdatTrnsRgba8Spec` describes a byte stream with a
multi-IDAT shape, a `tRNS` chunk between IHDR and the first IDAT, and
a target pixel type that is RGBA-8-bit (e.g. `PixelRGBA8`). The
runtime's `decodeBitmapWithMetadata` accepts such streams and applies
the transparency via `decodeRowsLoopRGBAWithTransparency`, returning a
`PngDecodeResult` with both the decoded bitmap and the parsed
metadata.

This is the forward-decode counterpart to
`decodeBitmap_rejects_of_transparency`: it shows that the *metadata-
aware* decoder, unlike `decodeBitmap`, threads transparency through
the pixel-decode chain instead of rejecting the stream. -/

structure ExternalPngMultiIdatTrnsRgba8Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  /-- The tRNS-bearing container: a `MultiIdatTrnsContainerSpec` whose
  `tRNS = some witness` (the chunk is mandatory in this forward spec). -/
  container : MultiIdatTrnsContainerSpec
  /-- The tRNS witness is present (this is the forward-decode path). -/
  trnsWitness : TrnsChunkWitness container.header
  hTrns : container.tRNS = some trnsWitness
  /-- Source bit depth is 8 (no up/down-sampling). -/
  hSourceBitDepth : container.header.bitDepth = 8
  /-- Target pixel type is 8-bit RGBA. -/
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hTargetColorType : PngPixel.colorType (α := px) = u8 6
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  /-- Narrows the container's {0, 1} interlace disjunction to = 0. -/
  hInterlace0 : container.header.interlace = 0
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType container.header.bitDepth =
        some (Pixel.bytesPerPixel (α := px))
  hIdatMin : 2 ≤ container.idatData.size
  inflatedRaw : ByteArray
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  hRawSize :
    inflatedRaw.size =
      bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)
  hPixels :
    decodeRowsLoopRGBAWithTransparency (some trnsWitness.trns) inflatedRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatTrnsRgba8Spec

variable {px : Type u} [Pixel px] [PngPixel px]

/-- Routing: `parsePngWithMetadata` accepts the container bytes and
returns the header + IDAT + tRNS-bearing metadata. -/
theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatTrnsRgba8Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatTrnsContainerSpec_correct

/-- The expected metadata for a `some trns` tRNS witness reduces to
`{ PngMetadata.empty with transparency := some trns }`. -/
lemma expectedMetadata_eq_trns (s : ExternalPngMultiIdatTrnsRgba8Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with transparency := some s.trnsWitness.trns } := by
  unfold MultiIdatTrnsContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatTrnsContainerSpec.toGeneric
  rw [s.hTrns]
  rfl

/-- The source color type is in {0, 2, 4, 6} (from the container's
`hColorType` disjunction). -/
lemma hSourceColorType (s : ExternalPngMultiIdatTrnsRgba8Spec px) :
    s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
  s.container.hColorType

/-- End-to-end closure: `decodeBitmapWithMetadata` accepts this stream
and returns the spec's bitmap + the original metadata. -/
theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatTrnsRgba8Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
  have hMeta := s.expectedMetadata_eq_trns
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
    rw [s.parsePngWithMetadata_external, hMeta]
  exact decodeBitmapWithMetadata_correct_of_witnesses_trnsRgba8
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hPxColorType s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatTrnsRgba8Spec

/-! ## 16-bit RGBA variant -/

/-- The 16-bit counterpart of `ExternalPngMultiIdatTrnsRgba8Spec`:
source bitDepth=16, target = 16-bit RGBA pixel type (e.g.
`PixelRGBA16`). The runtime routes through
`decodeRowsLoopRGBA16WithTransparency`. -/
structure ExternalPngMultiIdatTrnsRgba16Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatTrnsContainerSpec
  trnsWitness : TrnsChunkWitness container.header
  hTrns : container.tRNS = some trnsWitness
  /-- Source bit depth is 16. -/
  hSourceBitDepth : container.header.bitDepth = 16
  /-- Target pixel type is 16-bit RGBA. -/
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16
  hTargetColorType : PngPixel.colorType (α := px) = u8 6
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace0 : container.header.interlace = 0
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType container.header.bitDepth =
        some (Pixel.bytesPerPixel (α := px))
  hIdatMin : 2 ≤ container.idatData.size
  inflatedRaw : ByteArray
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  hRawSize :
    inflatedRaw.size =
      bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)
  hPixels :
    decodeRowsLoopRGBA16WithTransparency (some trnsWitness.trns)
        container.header.colorType inflatedRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatTrnsRgba16Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatTrnsRgba16Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatTrnsContainerSpec_correct

lemma expectedMetadata_eq_trns (s : ExternalPngMultiIdatTrnsRgba16Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with transparency := some s.trnsWitness.trns } := by
  unfold MultiIdatTrnsContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatTrnsContainerSpec.toGeneric
  rw [s.hTrns]
  rfl

lemma hSourceColorType (s : ExternalPngMultiIdatTrnsRgba16Spec px) :
    s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
  s.container.hColorType

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatTrnsRgba16Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
  have hMeta := s.expectedMetadata_eq_trns
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
    rw [s.parsePngWithMetadata_external, hMeta]
  exact decodeBitmapWithMetadata_correct_of_witnesses_trnsRgba16
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hPxColorType s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatTrnsRgba16Spec

/-! ## 16→8 downsample variant -/

/-- Source = 16-bit, target = 8-bit RGBA: the runtime downsamples via
`decodeRowsLoopDown16ToRGBA8WithTransparency`. -/
structure ExternalPngMultiIdatTrnsRgba16To8Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatTrnsContainerSpec
  trnsWitness : TrnsChunkWitness container.header
  hTrns : container.tRNS = some trnsWitness
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hTargetColorType : PngPixel.colorType (α := px) = u8 6
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace0 : container.header.interlace = 0
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  /-- Source 16-bit bpp for the container's color type. -/
  sourceBpp : Nat
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType 16 = some sourceBpp
  hIdatMin : 2 ≤ container.idatData.size
  inflatedRaw : ByteArray
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  hRawSize :
    inflatedRaw.size =
      bitmap.size.height * (bitmap.size.width * sourceBpp + 1)
  hPixels :
    decodeRowsLoopDown16ToRGBA8WithTransparency (some trnsWitness.trns)
        container.header.colorType inflatedRaw
        bitmap.size.width bitmap.size.height
        sourceBpp (bitmap.size.width * sourceBpp)
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatTrnsRgba16To8Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatTrnsRgba16To8Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatTrnsContainerSpec_correct

lemma expectedMetadata_eq_trns (s : ExternalPngMultiIdatTrnsRgba16To8Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with transparency := some s.trnsWitness.trns } := by
  unfold MultiIdatTrnsContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatTrnsContainerSpec.toGeneric
  rw [s.hTrns]
  rfl

lemma hSourceColorType (s : ExternalPngMultiIdatTrnsRgba16To8Spec px) :
    s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
  s.container.hColorType

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatTrnsRgba16To8Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
  have hMeta := s.expectedMetadata_eq_trns
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
    rw [s.parsePngWithMetadata_external, hMeta]
  exact decodeBitmapWithMetadata_correct_of_witnesses_trnsRgba16To8
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hPxColorType s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatTrnsRgba16To8Spec

/-! ## Adam7 (interlaced) variant -/

/-- The Adam7 interlaced counterpart of `ExternalPngMultiIdatTrnsRgba8Spec`:
`header.interlace = 1`. The decoder deinterlaces via
`decodeAdam7ToFlatRaw?` before applying the tRNS row-decoder. -/
structure ExternalPngMultiIdatTrnsRgba8Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatTrnsContainerSpec
  trnsWitness : TrnsChunkWitness container.header
  hTrns : container.tRNS = some trnsWitness
  hSourceBitDepth : container.header.bitDepth = 8
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hTargetColorType : PngPixel.colorType (α := px) = u8 6
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  /-- Narrows the container's {0, 1} interlace disjunction to = 1. -/
  hInterlace1 : container.header.interlace = 1
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType container.header.bitDepth =
        some (Pixel.bytesPerPixel (α := px))
  hIdatMin : 2 ≤ container.idatData.size
  inflatedRaw : ByteArray
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  /-- Deinterlaced row-major flat raw, produced by `decodeAdam7ToFlatRaw?`. -/
  flatRaw : ByteArray
  hAdam7 :
    decodeAdam7ToFlatRaw? inflatedRaw bitmap.size.width bitmap.size.height
      (Pixel.bytesPerPixel (α := px)) = some flatRaw
  hRawSize :
    flatRaw.size =
      bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)
  hPixels :
    decodeRowsLoopRGBAWithTransparency (some trnsWitness.trns) flatRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatTrnsRgba8Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatTrnsRgba8Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatTrnsContainerSpec_correct

lemma expectedMetadata_eq_trns (s : ExternalPngMultiIdatTrnsRgba8Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with transparency := some s.trnsWitness.trns } := by
  unfold MultiIdatTrnsContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatTrnsContainerSpec.toGeneric
  rw [s.hTrns]
  rfl

lemma hSourceColorType (s : ExternalPngMultiIdatTrnsRgba8Adam7Spec px) :
    s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
  s.container.hColorType

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatTrnsRgba8Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_trns]
  exact decodeBitmapWithMetadata_correct_of_witnesses_trnsRgba8_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hPxColorType s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatTrnsRgba8Adam7Spec

/-! ## 16-bit Adam7 variants -/

/-- Source = 16-bit RGBA, target = `PixelRGBA16`, Adam7 interlaced. -/
structure ExternalPngMultiIdatTrnsRgba16Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatTrnsContainerSpec
  trnsWitness : TrnsChunkWitness container.header
  hTrns : container.tRNS = some trnsWitness
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16
  hTargetColorType : PngPixel.colorType (α := px) = u8 6
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType container.header.bitDepth =
        some (Pixel.bytesPerPixel (α := px))
  hIdatMin : 2 ≤ container.idatData.size
  inflatedRaw : ByteArray
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  flatRaw : ByteArray
  hAdam7 :
    decodeAdam7ToFlatRaw? inflatedRaw bitmap.size.width bitmap.size.height
      (Pixel.bytesPerPixel (α := px)) = some flatRaw
  hRawSize :
    flatRaw.size =
      bitmap.size.height *
        (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)
  hPixels :
    decodeRowsLoopRGBA16WithTransparency (some trnsWitness.trns)
        container.header.colorType flatRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatTrnsRgba16Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatTrnsRgba16Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatTrnsContainerSpec_correct

lemma expectedMetadata_eq_trns (s : ExternalPngMultiIdatTrnsRgba16Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with transparency := some s.trnsWitness.trns } := by
  unfold MultiIdatTrnsContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatTrnsContainerSpec.toGeneric
  rw [s.hTrns]
  rfl

lemma hSourceColorType (s : ExternalPngMultiIdatTrnsRgba16Adam7Spec px) :
    s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
  s.container.hColorType

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatTrnsRgba16Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_trns]
  exact decodeBitmapWithMetadata_correct_of_witnesses_trnsRgba16_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hPxColorType s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatTrnsRgba16Adam7Spec

/-- Source = 16-bit, target = `PixelRGBA8` (downsample), Adam7 interlaced. -/
structure ExternalPngMultiIdatTrnsRgba16To8Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatTrnsContainerSpec
  trnsWitness : TrnsChunkWitness container.header
  hTrns : container.tRNS = some trnsWitness
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hTargetColorType : PngPixel.colorType (α := px) = u8 6
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
  hPxColorType : PngPixel.colorType (α := px) = u8 container.header.colorType
  sourceBpp : Nat
  hBppLookup :
    pngBytesPerPixelForColorTypeAndBitDepth?
      container.header.colorType 16 = some sourceBpp
  hIdatMin : 2 ≤ container.idatData.size
  inflatedRaw : ByteArray
  hInflated :
    zlibDecompressStored container.idatData hIdatMin = some inflatedRaw ∨
    (zlibDecompressStored container.idatData hIdatMin = none ∧
     zlibDecompress container.idatData hIdatMin = some inflatedRaw)
  flatRaw : ByteArray
  hAdam7 :
    decodeAdam7ToFlatRaw? inflatedRaw bitmap.size.width bitmap.size.height
      sourceBpp = some flatRaw
  hRawSize :
    flatRaw.size = bitmap.size.height * (bitmap.size.width * sourceBpp + 1)
  hPixels :
    decodeRowsLoopDown16ToRGBA8WithTransparency (some trnsWitness.trns)
        container.header.colorType flatRaw
        bitmap.size.width bitmap.size.height
        sourceBpp (bitmap.size.width * sourceBpp)
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatTrnsRgba16To8Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatTrnsRgba16To8Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatTrnsContainerSpec_correct

lemma expectedMetadata_eq_trns (s : ExternalPngMultiIdatTrnsRgba16To8Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with transparency := some s.trnsWitness.trns } := by
  unfold MultiIdatTrnsContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatTrnsContainerSpec.toGeneric
  rw [s.hTrns]
  rfl

lemma hSourceColorType (s : ExternalPngMultiIdatTrnsRgba16To8Adam7Spec px) :
    s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
  s.container.hColorType

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatTrnsRgba16To8Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with transparency := some s.trnsWitness.trns } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_trns]
  exact decodeBitmapWithMetadata_correct_of_witnesses_trnsRgba16To8_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hPxColorType s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatTrnsRgba16To8Adam7Spec

end Lemmas

end Bitmaps
