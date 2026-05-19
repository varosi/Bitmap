import Bitmap.Lemmas.MultiIdatTrnsExternalPngSpec
import Bitmap.Lemmas.MultiIdatBkgdAlphaExternalPngSpec
import Bitmap.Lemmas.Png.MultiIdatTrnsBkgdContainerSpec

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## tRNS + bKGD container forward-decode wrappers (RGB target)

These wrappers route a byte stream with both a tRNS chunk and a bKGD
chunk between IHDR and the first IDAT through the
`trnsRgb…` core theorems, which expect the parsed metadata to carry
both `transparency` and `background`. The new
`MultiIdatTrnsBkgdContainerSpec` provides the container and parser
witness for this layout. -/

/-! ### Source bd=8, target = `PixelRGB8` -/

structure ExternalPngMultiIdatTrnsBkgdRgb8Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatTrnsBkgdContainerSpec
  hSourceBitDepth : container.header.bitDepth = 8
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hTargetColorType : PngPixel.colorType (α := px) = u8 2
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
    decodeRowsLoopTrnsOverBackground container.trnsWitness.trns
        container.bkgdWitness.bkgd inflatedRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatTrnsBkgdRgb8Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatTrnsBkgdRgb8Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatTrnsBkgdContainerSpec_correct

lemma hSourceColorType (s : ExternalPngMultiIdatTrnsBkgdRgb8Spec px) :
    s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
  s.container.hColorType

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatTrnsBkgdRgb8Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata := { PngMetadata.empty with
                             transparency := some s.container.trnsWitness.trns
                             background := some s.container.bkgdWitness.bkgd } } := by
  have hMetaEq : s.container.expectedMetadata =
      { PngMetadata.empty with
          transparency := some s.container.trnsWitness.trns
          background := some s.container.bkgdWitness.bkgd } := rfl
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with
                               transparency := some s.container.trnsWitness.trns
                               background := some s.container.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, hMetaEq]
  exact decodeBitmapWithMetadata_correct_of_witnesses_trnsRgb8
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hPxColorType s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatTrnsBkgdRgb8Spec

/-! ### Source bd=16, target = `PixelRGB16` -/

structure ExternalPngMultiIdatTrnsBkgdRgb16Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatTrnsBkgdContainerSpec
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 16
  hTargetColorType : PngPixel.colorType (α := px) = u8 2
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
    decodeRowsLoopTrnsOverBackground16 container.trnsWitness.trns
        container.bkgdWitness.bkgd container.header.colorType inflatedRaw
        bitmap.size.width bitmap.size.height (Pixel.bytesPerPixel (α := px))
        (bitmap.size.width * Pixel.bytesPerPixel (α := px))
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatTrnsBkgdRgb16Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external (s : ExternalPngMultiIdatTrnsBkgdRgb16Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatTrnsBkgdContainerSpec_correct

lemma hSourceColorType (s : ExternalPngMultiIdatTrnsBkgdRgb16Spec px) :
    s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
  s.container.hColorType

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatTrnsBkgdRgb16Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata := { PngMetadata.empty with
                             transparency := some s.container.trnsWitness.trns
                             background := some s.container.bkgdWitness.bkgd } } := by
  have hMetaEq : s.container.expectedMetadata =
      { PngMetadata.empty with
          transparency := some s.container.trnsWitness.trns
          background := some s.container.bkgdWitness.bkgd } := rfl
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with
                               transparency := some s.container.trnsWitness.trns
                               background := some s.container.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, hMetaEq]
  exact decodeBitmapWithMetadata_correct_of_witnesses_trnsRgb16
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hPxColorType s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatTrnsBkgdRgb16Spec

/-! ### Source bd=16, target = `PixelRGB8` (downsample) -/

structure ExternalPngMultiIdatTrnsBkgdRgb16To8Spec (px : Type u) [Pixel px] [PngPixel px] where
  bitmap : Bitmap px
  container : MultiIdatTrnsBkgdContainerSpec
  hSourceBitDepth : container.header.bitDepth = 16
  hTargetBitDepth : PngPixel.bitDepth (α := px) = u8 8
  hTargetColorType : PngPixel.colorType (α := px) = u8 2
  hWidth : container.header.width = bitmap.size.width
  hHeight : container.header.height = bitmap.size.height
  hInterlace0 : container.header.interlace = 0
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
  hRawSize :
    inflatedRaw.size = bitmap.size.height * (bitmap.size.width * sourceBpp + 1)
  hPixels :
    decodeRowsLoopDown16TrnsOverBackgroundRGB8 container.trnsWitness.trns
        container.bkgdWitness.bkgd container.header.colorType inflatedRaw
        bitmap.size.width bitmap.size.height
        sourceBpp (bitmap.size.width * sourceBpp)
        0 0 ByteArray.empty
        { data := Array.replicate
            (bitmap.size.width * bitmap.size.height *
              Pixel.bytesPerPixel (α := px)) 0 } =
      some bitmap.data

namespace ExternalPngMultiIdatTrnsBkgdRgb16To8Spec

variable {px : Type u} [Pixel px] [PngPixel px]

theorem parsePngWithMetadata_external
    (s : ExternalPngMultiIdatTrnsBkgdRgb16To8Spec px) :
    parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
      some
        { header := s.container.header
          idat := s.container.idatData
          metadata := s.container.expectedMetadata } := by
  rw [← parsePngForDecode_eq_parsePngWithMetadata]
  exact s.container.parsePngForDecode_multiIdatTrnsBkgdContainerSpec_correct

lemma hSourceColorType (s : ExternalPngMultiIdatTrnsBkgdRgb16To8Spec px) :
    s.container.header.colorType = 0 ∨ s.container.header.colorType = 2 ∨
      s.container.header.colorType = 4 ∨ s.container.header.colorType = 6 :=
  s.container.hColorType

theorem decodeBitmapWithMetadata_external_correct
    (s : ExternalPngMultiIdatTrnsBkgdRgb16To8Spec px) :
    Png.decodeBitmapWithMetadata s.container.bytes =
      some { bitmap := s.bitmap
             metadata := { PngMetadata.empty with
                             transparency := some s.container.trnsWitness.trns
                             background := some s.container.bkgdWitness.bkgd } } := by
  have hMetaEq : s.container.expectedMetadata =
      { PngMetadata.empty with
          transparency := some s.container.trnsWitness.trns
          background := some s.container.bkgdWitness.bkgd } := rfl
  have hParse :
      parsePngWithMetadata s.container.bytes s.container.bytes_size_ge_8 =
        some { header := s.container.header
               idat := s.container.idatData
               metadata := { PngMetadata.empty with
                               transparency := some s.container.trnsWitness.trns
                               background := some s.container.bkgdWitness.bkgd } } := by
    rw [s.parsePngWithMetadata_external, hMetaEq]
  exact decodeBitmapWithMetadata_correct_of_witnesses_trnsRgb16To8
    s.container.bytes_size_ge_8 s.hSourceBitDepth s.hTargetBitDepth
    s.hSourceColorType s.hTargetColorType s.hWidth s.hHeight
    s.hInterlace0 s.hPxColorType s.hBppLookup hParse
    s.hIdatMin s.hInflated s.hRawSize s.hPixels

end ExternalPngMultiIdatTrnsBkgdRgb16To8Spec

end Lemmas

end Bitmaps
