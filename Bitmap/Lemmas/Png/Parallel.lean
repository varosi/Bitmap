import Bitmap.Png.Parallel
import Bitmap.Lemmas.Bitmap
import Bitmap.Lemmas.Png.PaletteEncoderRoundTrip

set_option lang.lemmaCmd true

universe u

namespace Bitmaps
namespace Lemmas

open Png

/-! ## Parallel PNG API equivalence

These lemmas pin the new task-based public entry points to the existing pure
PNG implementation. They let downstream proofs reuse the established sequential
container, zlib, row, and pixel correctness theorems unchanged.
-/

/-- Deterministic task evaluation returns the same value as direct evaluation.
This is the bridge from task scheduling back to the pure reference semantics. -/
@[simp] lemma parallelEval_eq {α : Type u}
    (options : PngParallelOptions) (workUnits workBytes : Nat) (f : Unit → α) :
    Png.parallelEval options workUnits workBytes f = f () := by
  unfold Png.parallelEval PngParallelOptions.useParallel
  split <;> rfl

/-- Parallel bitmap encoding is byte-for-byte equal to the existing encoder. -/
@[simp] lemma encodeBitmapParallel_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode) (parallel : PngParallelOptions) :
    Png.encodeBitmapParallel (px := px) bmp hw hh mode parallel =
      Png.encodeBitmap (px := px) bmp hw hh mode := by
  simp [Png.encodeBitmapParallel]

/-- Parallel option-aware bitmap encoding is equal to the existing encoder. -/
@[simp] lemma encodeBitmapWithOptionsParallel_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (options : PngEncodeOptions) (parallel : PngParallelOptions) :
    Png.encodeBitmapWithOptionsParallel (px := px) bmp hw hh options parallel =
      Png.encodeBitmapWithOptions (px := px) bmp hw hh options := by
  simp [Png.encodeBitmapWithOptionsParallel]

/-- Parallel checked bitmap encoding preserves the checked encoder result. -/
@[simp] lemma encodeBitmapCheckedParallel_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (mode : PngEncodeMode) (parallel : PngParallelOptions) :
    Png.encodeBitmapCheckedParallel (px := px) bmp mode parallel =
      Png.encodeBitmapChecked (px := px) bmp mode := by
  simp [Png.encodeBitmapCheckedParallel]

/-- Parallel checked option-aware bitmap encoding preserves the checked result. -/
@[simp] lemma encodeBitmapWithOptionsCheckedParallel_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (options : PngEncodeOptions) (parallel : PngParallelOptions) :
    Png.encodeBitmapWithOptionsCheckedParallel (px := px) bmp options parallel =
      Png.encodeBitmapWithOptionsChecked (px := px) bmp options := by
  simp [Png.encodeBitmapWithOptionsCheckedParallel]

/-- Parallel bitmap decoding returns the same result as the existing decoder. -/
@[simp] lemma decodeBitmapParallel_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bytes : ByteArray) (parallel : PngParallelOptions) :
    Png.decodeBitmapParallel (px := px) bytes parallel =
      Png.decodeBitmap (px := px) bytes := by
  simp [Png.decodeBitmapParallel]

/-- Parallel metadata-aware bitmap decoding preserves the existing result. -/
@[simp] lemma decodeBitmapWithMetadataParallel_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bytes : ByteArray) (parallel : PngParallelOptions) :
    Png.decodeBitmapWithMetadataParallel (px := px) bytes parallel =
      Png.decodeBitmapWithMetadata (px := px) bytes := by
  simp [Png.decodeBitmapWithMetadataParallel]

/-- Parallel Gray1 encoding is byte-for-byte equal to the existing encoder. -/
@[simp] lemma encodeGray1BitmapParallel_eq
    (bmp : Bitmap.Gray1)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode) (parallel : PngParallelOptions) :
    Png.encodeGray1BitmapParallel bmp hw hh mode parallel =
      Png.encodeGray1Bitmap bmp hw hh mode := by
  simp [Png.encodeGray1BitmapParallel]

/-- Parallel option-aware Gray1 encoding is equal to the existing encoder. -/
@[simp] lemma encodeGray1BitmapWithOptionsParallel_eq
    (bmp : Bitmap.Gray1)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (options : PngEncodeOptions) (parallel : PngParallelOptions) :
    Png.encodeGray1BitmapWithOptionsParallel bmp hw hh options parallel =
      Png.encodeGray1BitmapWithOptions bmp hw hh options := by
  simp [Png.encodeGray1BitmapWithOptionsParallel]

/-- Parallel checked Gray1 encoding preserves the existing checked result. -/
@[simp] lemma encodeGray1BitmapCheckedParallel_eq
    (bmp : Bitmap.Gray1) (mode : PngEncodeMode) (parallel : PngParallelOptions) :
    Png.encodeGray1BitmapCheckedParallel bmp mode parallel =
      Png.encodeGray1BitmapChecked bmp mode := by
  simp [Png.encodeGray1BitmapCheckedParallel]

/-- Parallel checked option-aware Gray1 encoding preserves the checked result. -/
@[simp] lemma encodeGray1BitmapWithOptionsCheckedParallel_eq
    (bmp : Bitmap.Gray1) (options : PngEncodeOptions) (parallel : PngParallelOptions) :
    Png.encodeGray1BitmapWithOptionsCheckedParallel bmp options parallel =
      Png.encodeGray1BitmapWithOptionsChecked bmp options := by
  simp [Png.encodeGray1BitmapWithOptionsCheckedParallel]

/-- Parallel Gray1 decoding returns the same result as the existing decoder. -/
@[simp] lemma decodeGray1BitmapParallel_eq
    (bytes : ByteArray) (parallel : PngParallelOptions) :
    Png.decodeGray1BitmapParallel bytes parallel =
      Png.decodeGray1Bitmap bytes := by
  simp [Png.decodeGray1BitmapParallel]

/-- Parallel metadata-aware Gray1 decoding preserves the existing result. -/
@[simp] lemma decodeGray1BitmapWithMetadataParallel_eq
    (bytes : ByteArray) (parallel : PngParallelOptions) :
    Png.decodeGray1BitmapWithMetadataParallel bytes parallel =
      Png.decodeGray1BitmapWithMetadata bytes := by
  simp [Png.decodeGray1BitmapWithMetadataParallel]

/-- Parallel indexed encoding is byte-for-byte equal to the existing encoder. -/
@[simp] lemma encodeIndexedBitmapWithOptionsParallel_eq
    (bmp : PngIndexedBitmap) (options : PngEncodeOptions)
    (parallel : PngParallelOptions) :
    Png.encodeIndexedBitmapWithOptionsParallel bmp options parallel =
      Png.encodeIndexedBitmapWithOptions bmp options := by
  simp [Png.encodeIndexedBitmapWithOptionsParallel]

/-- Parallel checked indexed encoding preserves the existing checked result. -/
@[simp] lemma encodeIndexedBitmapWithOptionsCheckedParallel_eq
    (bmp : PngIndexedBitmap) (options : PngEncodeOptions)
    (parallel : PngParallelOptions) :
    Png.encodeIndexedBitmapWithOptionsCheckedParallel bmp options parallel =
      Png.encodeIndexedBitmapWithOptionsChecked bmp options := by
  simp [Png.encodeIndexedBitmapWithOptionsCheckedParallel]

/-- Parallel checked indexed encoding by mode preserves the existing result. -/
@[simp] lemma encodeIndexedBitmapCheckedParallel_eq
    (bmp : PngIndexedBitmap) (mode : PngEncodeMode)
    (parallel : PngParallelOptions) :
    Png.encodeIndexedBitmapCheckedParallel bmp mode parallel =
      Png.encodeIndexedBitmapChecked bmp mode := by
  simp [Png.encodeIndexedBitmapCheckedParallel]

/-- Parallel indexed metadata-aware decoding preserves the existing result. -/
@[simp] lemma decodeIndexedBitmapWithMetadataParallel_eq
    (bytes : ByteArray) (parallel : PngParallelOptions) :
    Png.decodeIndexedBitmapWithMetadataParallel bytes parallel =
      Png.decodeIndexedBitmapWithMetadata bytes := by
  simp [Png.decodeIndexedBitmapWithMetadataParallel]

/-- Parallel indexed decoding preserves the existing result. -/
@[simp] lemma decodeIndexedBitmapParallel_eq
    (bytes : ByteArray) (parallel : PngParallelOptions) :
    Png.decodeIndexedBitmapParallel bytes parallel =
      Png.decodeIndexedBitmap bytes := by
  simp [Png.decodeIndexedBitmapParallel]

/-- End-to-end bitmap round trips through parallel encode and decode reduce to
the established sequential PNG round-trip theorem. -/
lemma decodeBitmapParallel_encodeBitmapParallel {px : Type u}
    [PixelFormat px] [Png.PixelFormat px] [PngRoundTrip px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode)
    (parallelEncode parallelDecode : PngParallelOptions)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := mode)).size < 2 ^ 32) :
    Png.decodeBitmapParallel (px := px)
        (Png.encodeBitmapParallel (px := px) bmp hw hh mode parallelEncode)
        parallelDecode =
      some bmp := by
  rw [decodeBitmapParallel_eq, encodeBitmapParallel_eq]
  exact decodeBitmap_encodeBitmap (bmp := bmp)
    (hw := by simpa [UInt32.size] using hw)
    (hh := by simpa [UInt32.size] using hh)
    (mode := mode) hidat

/-- Indexed-palette data round trips through parallel checked encode and
parallel decode whenever the existing sequential palette theorem applies. -/
theorem decodeIndexedBitmapParallel_encodeIndexedBitmapCheckedParallel_paletteRange_data
    (mode : PngEncodeMode)
    (bmp : PngIndexedBitmap)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (hbd : bmp.bitDepth = 1 ∨ bmp.bitDepth = 2 ∨ bmp.bitDepth = 4 ∨ bmp.bitDepth = 8)
    (hpalNonempty : bmp.palette.entries.size ≠ 0)
    (hpalTriplets : bmp.palette.entries.size % 3 = 0)
    (hpalMax : bmp.palette.entries.size ≤ 256 * 3)
    (hpalFits : bmp.palette.entryCount ≤ paletteIndexLimit bmp.bitDepth)
    (hrange :
      ∀ y, y < bmp.size.height → ∀ x, x < bmp.size.width →
        (bmp.data.get! (y * bmp.size.width + x)).toNat < bmp.palette.entryCount)
    (htrans : bmp.transparency = none)
    (hbg : bmp.background = none)
    (parallelEncode parallelDecode : PngParallelOptions)
    (hIdatSize :
      (match mode with
       | .stored => zlibCompressStored (encodeRawIndexedWithFilter bmp .none)
       | .fixed => zlibCompressFixed (encodeRawIndexedWithFilter bmp .none)
       | .dynamic => zlibCompressDynamic (encodeRawIndexedWithFilter bmp .none)).size
        < 2 ^ 32) :
    ∃ bytes,
      Png.encodeIndexedBitmapCheckedParallel bmp mode parallelEncode = Except.ok bytes ∧
        (Png.decodeIndexedBitmapWithMetadataParallel bytes parallelDecode).map
            (fun result => result.bitmap.data) =
          some bmp.data ∧
        (Png.decodeIndexedBitmapParallel bytes parallelDecode).map
            (fun bitmap => bitmap.data) = some bmp.data := by
  rcases
    PaletteEncoderRoundTrip.decodeIndexedBitmap_encodeIndexedBitmapChecked_paletteRange_data
      mode bmp hw hh hbd hpalNonempty hpalTriplets hpalMax hpalFits
      hrange htrans hbg hIdatSize with ⟨bytes, henc, hmetadata, hpixel⟩
  exact ⟨bytes, by simpa using henc, by simpa using hmetadata, by simpa using hpixel⟩

end Lemmas
end Bitmaps
