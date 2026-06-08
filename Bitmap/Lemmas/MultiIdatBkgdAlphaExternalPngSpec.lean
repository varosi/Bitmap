import Bitmap.Lemmas.MultiIdatBkgdExternalPngSpec
import Bitmap.Lemmas.ExternalPngCore
import Bitmap.Lemmas.Png.MultiIdatBkgdContainerSpec

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## AlphaOverBackground forward-decode wrappers

When the parsed metadata has `transparency = none` and
`background = some bg`, and the source color type is 4 (gray+alpha)
or 6 (RGBA), `decodeBitmapWithMetadata` composites the source alpha
against the background. These wrappers route the byte stream through
`MultiIdatBkgdContainerSpec` (which provides the bKGD chunk needed to
materialise `bg`) to one of the `alphaBg…` core theorems. -/

/-! ### Source ct=4 → target gray8 -/

structure ExternalPngMultiIdatAlphaBgGray8Spec (px : Type u) [Pixel px] [PngPixel px] where
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
  hInterlace0 : container.header.interlace = 0
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
    decodeRowsLoopGrayAlphaOverBackground bkgdWitness.bkgd inflatedRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgGray8Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgGray8Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgGray8Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgGray8Spec px) :
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
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgGray8
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgGray8Spec

/-! ### Source ct=4 → target gray16 -/

structure ExternalPngMultiIdatAlphaBgGray16Spec (px : Type u) [Pixel px] [PngPixel px] where
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
  hInterlace0 : container.header.interlace = 0
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
    decodeRowsLoopGrayAlphaOverBackground16 bkgdWitness.bkgd
        container.header.colorType inflatedRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgGray16Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgGray16Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgGray16Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgGray16Spec px) :
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
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgGray16
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgGray16Spec

/-! ### Source ct=4 → target RGB8 -/

structure ExternalPngMultiIdatAlphaBgRgb8Spec (px : Type u) [Pixel px] [PngPixel px] where
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
  hInterlace0 : container.header.interlace = 0
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
    decodeRowsLoopAlphaOverBackground bkgdWitness.bkgd inflatedRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgb8Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgRgb8Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgRgb8Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgb8Spec px) :
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
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgb8
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgb8Spec

/-! ### Source ct=4 bd=16 → target gray8 (downsample) -/

structure ExternalPngMultiIdatAlphaBgGray16To8Spec (px : Type u) [Pixel px] [PngPixel px] where
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
  hInterlace0 : container.header.interlace = 0
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
    inflatedRaw.size = bitmap.size.height * (bitmap.size.width * sourceBpp + 1)
  hPixels :
    decodeRowsLoopDown16GrayAlphaOverBackgroundGray8 bkgdWitness.bkgd
        container.header.colorType inflatedRaw
        bitmap.size.width bitmap.size.height
        sourceBpp (bitmap.size.width * sourceBpp)
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgGray16To8Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgGray16To8Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgGray16To8Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgGray16To8Spec px) :
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
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgGray16To8
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgGray16To8Spec

/-! ### Source ct=4 → target RGB16 -/

structure ExternalPngMultiIdatAlphaBgRgb16Spec (px : Type u) [Pixel px] [PngPixel px] where
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
  hInterlace0 : container.header.interlace = 0
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
    decodeRowsLoopAlphaOverBackground16 bkgdWitness.bkgd
        container.header.colorType inflatedRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgb16Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgRgb16Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgRgb16Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgb16Spec px) :
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
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgb16
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgb16Spec

/-! ### Source ct=6 (RGBA) → target RGB8 -/

structure ExternalPngMultiIdatAlphaBgRgba6To2Spec (px : Type u) [Pixel px] [PngPixel px] where
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
  hInterlace0 : container.header.interlace = 0
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
    decodeRowsLoopAlphaOverBackground bkgdWitness.bkgd inflatedRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgba6To2Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgRgba6To2Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgRgba6To2Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgba6To2Spec px) :
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
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgba6To2
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgba6To2Spec

/-! ### Source ct=6 (RGBA) → target RGB16 -/

structure ExternalPngMultiIdatAlphaBgRgba6To2_16Spec (px : Type u) [Pixel px] [PngPixel px] where
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
  hInterlace0 : container.header.interlace = 0
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
    decodeRowsLoopAlphaOverBackground16 bkgdWitness.bkgd
        container.header.colorType inflatedRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgba6To2_16Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatAlphaBgRgba6To2_16Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgRgba6To2_16Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgba6To2_16Spec px) :
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
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgba6To2_16
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgba6To2_16Spec

/-! ### Source ct=6 bd=16 (RGBA) → target RGB8 (downsample) -/

structure ExternalPngMultiIdatAlphaBgRgba6To2_16To8Spec (px : Type u) [Pixel px] [PngPixel px] where
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
  hInterlace0 : container.header.interlace = 0
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
    inflatedRaw.size = bitmap.size.height * (bitmap.size.width * sourceBpp + 1)
  hPixels :
    decodeRowsLoopDown16AlphaOverBackgroundRGB8 bkgdWitness.bkgd
        container.header.colorType inflatedRaw
        bitmap.size.width bitmap.size.height
        sourceBpp (bitmap.size.width * sourceBpp)
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatAlphaBgRgba6To2_16To8Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external
    (s : ExternalPngMultiIdatAlphaBgRgba6To2_16To8Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatBkgdContainerSpec_correct

lemma expectedMetadata_eq_bg (s : ExternalPngMultiIdatAlphaBgRgba6To2_16To8Spec px) :
    s.container.expectedMetadata =
      { PngMetadata.empty with background := some s.bkgdWitness.bkgd } := by
  unfold MultiIdatBkgdContainerSpec.expectedMetadata
    MultiIdatGenericPreChunkContainerSpec.expectedMetadata
    MultiIdatBkgdContainerSpec.toGeneric
  rw [s.hBkgd]
  rfl

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatAlphaBgRgba6To2_16To8Spec px) :
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
  exact decodeBitmapWithMetadata_correct_of_witnesses_alphaBgRgba6To2_16To8
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatAlphaBgRgba6To2_16To8Spec

end Lemmas

end Bitmaps
