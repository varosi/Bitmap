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

end Lemmas

end Bitmaps
