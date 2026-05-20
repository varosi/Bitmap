import Bitmap.Lemmas.MultiIdatBkgdAlphaExternalPngSpec

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## AlphaOverBackground + Adam7 wrappers

User-facing wrappers around the alpha-bg + Adam7 core theorems. Each
wrapper carries a `MultiIdatBkgdContainerSpec` (whose `hInterlace`
field admits {0, 1}) narrowed to `interlace = 1`, plus the
Adam7-deinterlaced flat raw and the appropriate decode-rows witness.

There are 9 variants covering source color types {4, 6} × target
color types {gray, RGB} × source bit depth {8, 16} (with downsample
combinations); each mirrors the corresponding non-Adam7 wrapper in
`MultiIdatBkgdAlphaExternalPngSpec.lean`. -/

/-! ### Source ct=4 → target gray8 (Adam7) -/

structure ExternalPngMultiIdatAlphaBgGray8Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatBkgdContainerSpec
  bkgdWitness : BkgdChunkWitness container.header
  hBkgd : container.bKGD = some bkgdWitness
  hSourceBitDepth : container.header.bitDepth = 8
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hSourceColorType : container.header.colorType = 4
  hTargetColorType : PngPixel.colorType (α := px) = u8 0
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
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
    decodeRowsLoopGrayAlphaOverBackground bkgdWitness.bkgd flatRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgGray8Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgGray8Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgGray8Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgGray8Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_bg]
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgGray8_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgGray8Adam7Spec

/-! ### Source ct=4 → target gray16 (Adam7) -/

structure ExternalPngMultiIdatAlphaBgGray16Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatBkgdContainerSpec
  bkgdWitness : BkgdChunkWitness container.header
  hBkgd : container.bKGD = some bkgdWitness
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16
  hSourceColorType : container.header.colorType = 4
  hTargetColorType : PngPixel.colorType (α := px) = u8 0
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
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
    decodeRowsLoopGrayAlphaOverBackground16 bkgdWitness.bkgd
        container.header.colorType flatRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgGray16Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgGray16Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgGray16Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgGray16Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_bg]
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgGray16_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgGray16Adam7Spec

/-! ### Source ct=4 bd=16 → target gray8 (Adam7 downsample) -/

structure ExternalPngMultiIdatAlphaBgGray16To8Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatBkgdContainerSpec
  bkgdWitness : BkgdChunkWitness container.header
  hBkgd : container.bKGD = some bkgdWitness
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hSourceColorType : container.header.colorType = 4
  hTargetColorType : PngPixel.colorType (α := px) = u8 0
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
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
    decodeRowsLoopDown16GrayAlphaOverBackgroundGray8 bkgdWitness.bkgd
        container.header.colorType flatRaw
        bitmap.size.width bitmap.size.height
        sourceBpp (bitmap.size.width * sourceBpp)
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgGray16To8Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external
    (s : ExternalPngMultiIdatAlphaBgGray16To8Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgGray16To8Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgGray16To8Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_bg]
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgGray16To8_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgGray16To8Adam7Spec

/-! ### Source ct=4 → target RGB8 (Adam7) -/

structure ExternalPngMultiIdatAlphaBgRgb8Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatBkgdContainerSpec
  bkgdWitness : BkgdChunkWitness container.header
  hBkgd : container.bKGD = some bkgdWitness
  hSourceBitDepth : container.header.bitDepth = 8
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hSourceColorType : container.header.colorType = 4
  hTargetColorType : PngPixel.colorType (α := px) = u8 2
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
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
    decodeRowsLoopAlphaOverBackground bkgdWitness.bkgd flatRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgb8Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgRgb8Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgRgb8Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgb8Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_bg]
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgb8_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgb8Adam7Spec

/-! ### Source ct=4 bd=16 → target RGB16 (Adam7) -/

structure ExternalPngMultiIdatAlphaBgRgb16Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatBkgdContainerSpec
  bkgdWitness : BkgdChunkWitness container.header
  hBkgd : container.bKGD = some bkgdWitness
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16
  hSourceColorType : container.header.colorType = 4
  hTargetColorType : PngPixel.colorType (α := px) = u8 2
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
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
    decodeRowsLoopAlphaOverBackground16 bkgdWitness.bkgd
        container.header.colorType flatRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgb16Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgRgb16Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgRgb16Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgb16Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_bg]
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgb16_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgb16Adam7Spec

/-! ### Source ct=4 bd=16 → target RGB8 (Adam7 downsample) -/

structure ExternalPngMultiIdatAlphaBgRgb16To8Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatBkgdContainerSpec
  bkgdWitness : BkgdChunkWitness container.header
  hBkgd : container.bKGD = some bkgdWitness
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hSourceColorType : container.header.colorType = 4
  hTargetColorType : PngPixel.colorType (α := px) = u8 2
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
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
    decodeRowsLoopDown16AlphaOverBackgroundRGB8 bkgdWitness.bkgd
        container.header.colorType flatRaw
        bitmap.size.width bitmap.size.height
        sourceBpp (bitmap.size.width * sourceBpp)
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgb16To8Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external
    (s : ExternalPngMultiIdatAlphaBgRgb16To8Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgRgb16To8Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgb16To8Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_bg]
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgb16To8_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgb16To8Adam7Spec

/-! ### Source ct=6 → target RGB8 (Adam7) -/

structure ExternalPngMultiIdatAlphaBgRgba6To2Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatBkgdContainerSpec
  bkgdWitness : BkgdChunkWitness container.header
  hBkgd : container.bKGD = some bkgdWitness
  hSourceBitDepth : container.header.bitDepth = 8
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hSourceColorType : container.header.colorType = 6
  hTargetColorType : PngPixel.colorType (α := px) = u8 2
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
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
    decodeRowsLoopAlphaOverBackground bkgdWitness.bkgd flatRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgba6To2Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external
    (s : ExternalPngMultiIdatAlphaBgRgba6To2Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgRgba6To2Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgba6To2Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_bg]
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgba6To2_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgba6To2Adam7Spec

/-! ### Source ct=6 bd=16 → target RGB16 (Adam7) -/

structure ExternalPngMultiIdatAlphaBgRgba6To2_16Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatBkgdContainerSpec
  bkgdWitness : BkgdChunkWitness container.header
  hBkgd : container.bKGD = some bkgdWitness
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16
  hSourceColorType : container.header.colorType = 6
  hTargetColorType : PngPixel.colorType (α := px) = u8 2
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
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
    decodeRowsLoopAlphaOverBackground16 bkgdWitness.bkgd
        container.header.colorType flatRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgba6To2_16Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external
    (s : ExternalPngMultiIdatAlphaBgRgba6To2_16Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg
    (s : ExternalPngMultiIdatAlphaBgRgba6To2_16Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgba6To2_16Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_bg]
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgba6To2_16_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgba6To2_16Adam7Spec

/-! ### Source ct=6 bd=16 → target RGB8 (Adam7 downsample) -/

structure ExternalPngMultiIdatAlphaBgRgba6To2_16To8Adam7Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatBkgdContainerSpec
  bkgdWitness : BkgdChunkWitness container.header
  hBkgd : container.bKGD = some bkgdWitness
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hSourceColorType : container.header.colorType = 6
  hTargetColorType : PngPixel.colorType (α := px) = u8 2
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace1 : container.header.interlace = 1
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
    decodeRowsLoopDown16AlphaOverBackgroundRGB8 bkgdWitness.bkgd
        container.header.colorType flatRaw
        bitmap.size.width bitmap.size.height
        sourceBpp (bitmap.size.width * sourceBpp)
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgba6To2_16To8Adam7Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external
    (s : ExternalPngMultiIdatAlphaBgRgba6To2_16To8Adam7Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg
    (s : ExternalPngMultiIdatAlphaBgRgba6To2_16To8Adam7Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgba6To2_16To8Adam7Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata :=
               { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with background := some s.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, s.expectedMetadata_eq_bg]
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgba6To2_16To8_adam7
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace1 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hAdam7 s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgba6To2_16To8Adam7Spec

end Lemmas

end Bitmaps
