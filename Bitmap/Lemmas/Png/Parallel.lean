import Bitmap.Png.Parallel
import Bitmap.Lemmas.Bitmap
import Bitmap.Lemmas.Png.PaletteEncoderRoundTrip

set_option lang.lemmaCmd true

universe u v

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

/-- Getting a spawned pure task returns the same deterministic value. This keeps
helper proofs small when several independent PNG chunks are spawned together. -/
@[simp] lemma taskSpawn_get_eq {α : Type u} (f : Unit → α) :
    (Task.spawn f).get = f () := by
  rfl

/-- List-level task mapping preserves deterministic list mapping. Stored-block
parallelism uses this to recover the ordered sequential block stream. -/
@[simp] lemma mapListParallel_eq_map {α : Type u} {β : Type v}
    (xs : List α) (f : α → β) :
    Png.mapListParallel xs f = xs.map f := by
  unfold Png.mapListParallel
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [ih]

/-- Canonical one-shard options for segmented fixed-Huffman proof reductions.
With these options, the segmented encoder must collapse to the sequential path. -/
def oneShardPngParallelOptions : PngParallelOptions :=
  { maxShards := 1, minRowsPerShard := 1, targetBytesPerShard := 1 }

/-- Simplifies the scheduler cap when `maxShards = 1`.
This small arithmetic fact keeps one-shard segmented proofs local. -/
lemma nat_max_one_min_one (n : Nat) : Nat.max 1 (Nat.min 1 n) = 1 := by
  cases n <;> rfl

/-- One-shard parallel options always select exactly one shard.
This proves the segmented fixed encoder has no extra block split in that mode. -/
@[simp] lemma shardCountForWork_oneShardPngParallelOptions
    (workUnits workBytes : Nat) :
    PngParallelOptions.shardCountForWork oneShardPngParallelOptions
        workUnits workBytes = 1 := by
  simp [oneShardPngParallelOptions, PngParallelOptions.shardCountForWork,
    PngParallelOptions.normalizedMaxShards, Png.parallelCeilDiv,
    nat_max_one_min_one]

/-- Byte sharding with one-shard options returns the whole input range.
This bridges segmented fixed-Huffman tokenization back to the sequential input. -/
@[simp] lemma byteShardRanges_oneShardPngParallelOptions (raw : ByteArray) :
    Png.byteShardRanges oneShardPngParallelOptions raw.size =
      [{ start := 0, stop := raw.size }] := by
  simp [Png.byteShardRanges, Png.shardRanges]

/-- Stored-block range descriptors materialize to the same bytes as running
the existing stored DEFLATE encoder on the corresponding raw-buffer slice. -/
lemma storedDeflateBlockRangesFrom_correct
    (source : ByteArray) (offset remaining : Nat)
    (hbound : offset + remaining ≤ source.size) :
    Png.concatByteArrays
        ((Png.storedDeflateBlockRangesFrom offset remaining).map
          fun range => range.toBlock source) =
      Png.deflateStored (source.extract offset (offset + remaining)) := by
  classical
  induction remaining using Nat.strong_induction_on generalizing offset with
  | h remaining ih =>
      by_cases hzero : remaining = 0
      · subst remaining
        rw [Png.storedDeflateBlockRangesFrom.eq_1]
        simp [Png.concatByteArrays, Png.StoredDeflateBlockRange.toBlock]
        rw [Png.deflateStored.eq_1]
        simp
      · have hpos_remaining : 0 < remaining := Nat.pos_of_ne_zero hzero
        let blockLen := Nat.min Png.uint16MaxValue remaining
        let stop := offset + blockLen
        have hle : blockLen ≤ remaining := by
          simpa [blockLen] using Nat.min_le_right Png.uint16MaxValue remaining
        have hpos_block : 0 < blockLen := by
          have hpos_max : 0 < Png.uint16MaxValue := by
            simp [Png.uint16MaxValue, UInt16.size]
          rw [Nat.lt_min]
          exact ⟨hpos_max, hpos_remaining⟩
        have hsliceSize :
            (source.extract offset (offset + remaining)).size = remaining := by
          simp [ByteArray.size_extract]
          omega
        have hpayload :
            (source.extract offset (offset + remaining)).extract 0 blockLen =
              source.extract offset stop := by
          have hExt := ByteArray.extract_extract (a := source) (i := offset)
            (j := offset + remaining) (k := 0) (l := blockLen)
          have hmin : min (offset + blockLen) (offset + remaining) = offset + blockLen := by
            omega
          simpa [stop, hmin] using hExt
        by_cases hfinal : blockLen = remaining
        · have hbeq : (blockLen == remaining) = true := by
            simp [hfinal]
          have hstop : stop = offset + remaining := by
            simp [stop, hfinal]
          rw [Png.deflateStored.eq_1]
          rw [Png.storedDeflateBlockRangesFrom.eq_1]
          simp [Png.concatByteArrays, Png.StoredDeflateBlockRange.toBlock,
            hzero, blockLen, stop, hbeq, hsliceSize, hpayload, hstop]
        · have hbeq : (blockLen == remaining) = false := beq_false_of_ne hfinal
          have hrestBound : stop + (remaining - blockLen) ≤ source.size := by
            simp [stop]
            omega
          have hrestSize : remaining - blockLen < remaining :=
            Nat.sub_lt_self hpos_block hle
          have hrest :=
            ih (remaining - blockLen) hrestSize stop hrestBound
          have hrestExtract :
              (source.extract offset (offset + remaining)).extract blockLen remaining =
                source.extract stop (stop + (remaining - blockLen)) := by
            have hExt := ByteArray.extract_extract (a := source) (i := offset)
              (j := offset + remaining) (k := blockLen) (l := remaining)
            have hmin : min (offset + remaining) (offset + remaining) =
                offset + remaining := by simp
            have hstopRemaining : offset + remaining = stop + (remaining - blockLen) := by
              simp [stop]
              omega
            simpa [stop, hmin, hstopRemaining] using hExt
          rw [Png.deflateStored.eq_1]
          rw [Png.storedDeflateBlockRangesFrom.eq_1]
          simp [Png.concatByteArrays, Png.StoredDeflateBlockRange.toBlock,
            hzero, blockLen, stop, hbeq, hsliceSize, hpayload, hrestExtract]
          simpa [Png.concatByteArrays, Png.StoredDeflateBlockRange.toBlock, stop]
            using hrest

/-- The stored-block range implementation is byte-for-byte equal to the
existing stored DEFLATE encoder for the whole raw payload. -/
@[simp] lemma deflateStoredByBlocks_eq (raw : ByteArray) :
    Png.deflateStoredByBlocks raw = Png.deflateStored raw := by
  have h := storedDeflateBlockRangesFrom_correct raw 0 raw.size (by simp)
  simpa [Png.deflateStoredByBlocks, Png.storedDeflateBlockRanges,
    ByteArray.extract_zero_size] using h

/-- Stored block tasks preserve the exact stored DEFLATE byte stream. -/
@[simp] lemma deflateStoredParallel_eq
    (raw : ByteArray) (parallel : PngParallelOptions) :
    Png.deflateStoredParallel raw parallel = Png.deflateStored raw := by
  unfold Png.deflateStoredParallel
  by_cases h :
      (parallel.useParallel (Png.storedDeflateBlockRanges raw).length raw.size &&
        decide (parallel.minRowsPerShard ≤ (Png.storedDeflateBlockRanges raw).length) &&
        decide ((Png.storedDeflateBlockRanges raw).length ≤
          parallel.normalizedMaxShards)) = true
  · simpa [h, Png.deflateStoredByBlocks] using (deflateStoredByBlocks_eq raw)
  · simp [h]

/-- Parallel zlib wrapper construction preserves the existing envelope shape.
This justifies spawning deflate payload generation and Adler checksum
independently without changing bytes. -/
@[simp] lemma zlibCompressWithParallel_eq
    (deflate : ByteArray → ByteArray) (raw : ByteArray) (parallel : PngParallelOptions) :
    Png.zlibCompressWithParallel deflate raw parallel =
      (let header := ByteArray.mk #[Png.u8 0x78, Png.u8 0x01]
       let deflated := deflate raw
       let adler := Png.u32be (Png.adler32 raw).toNat
       let outSize := header.size + deflated.size + adler.size
       let out := ByteArray.emptyWithCapacity outSize
       out ++ header ++ deflated ++ adler) := by
  unfold Png.zlibCompressWithParallel
  split <;> rfl

/-- Parallel stored compression preserves the existing stored zlib stream. -/
@[simp] lemma zlibCompressStoredParallel_eq
    (raw : ByteArray) (parallel : PngParallelOptions) :
    Png.zlibCompressStoredParallel raw parallel = Png.zlibCompressStored raw := by
  simp [Png.zlibCompressStoredParallel, Png.zlibCompressStored]

/-- Parallel stored decompression preserves the existing stored-only zlib
decoder result byte-for-byte. -/
@[simp] lemma zlibDecompressStoredParallel_eq
    (data : ByteArray) (hsize : 2 <= data.size) (parallel : PngParallelOptions) :
    Png.zlibDecompressStoredParallel data hsize parallel =
      Png.zlibDecompressStored data hsize := by
  simp [Png.zlibDecompressStoredParallel]

/-- Parallel fixed compression preserves the existing fixed-Huffman zlib stream. -/
@[simp] lemma zlibCompressFixedParallel_eq
    (raw : ByteArray) (parallel : PngParallelOptions) :
    Png.zlibCompressFixedParallel raw parallel = Png.zlibCompressFixed raw := by
  simp [Png.zlibCompressFixedParallel, Png.zlibCompressFixed]

/-- One-shard segmented fixed-Huffman DEFLATE is byte-for-byte equal to the
existing fixed-Huffman encoder. It validates the segmented path's base case. -/
@[simp] lemma deflateFixedSegmentedParallel_oneShard_eq (raw : ByteArray) :
    Png.deflateFixedSegmentedParallel raw oneShardPngParallelOptions =
      Png.deflateFixed raw := by
  simp [Png.deflateFixedSegmentedParallel, Png.PngParallelOptions.useParallel,
    Png.fixedLz77ShardTokens, Png.writeFixedLz77Blocks, Png.writeFixedLz77Block,
    Png.deflateFixed, Png.deflateFixedLz77, ByteArray.extract_zero_size]

/-- One-shard segmented fixed-Huffman zlib compression preserves the existing
fixed zlib bytes, including the wrapper and Adler checksum. -/
@[simp] lemma zlibCompressFixedSegmentedParallel_oneShard_eq (raw : ByteArray) :
    Png.zlibCompressFixedSegmentedParallel raw oneShardPngParallelOptions =
      Png.zlibCompressFixed raw := by
  simp [Png.zlibCompressFixedSegmentedParallel, Png.zlibCompressFixed]

/-- Parallel dynamic compression preserves the existing dynamic-Huffman zlib stream. -/
@[simp] lemma zlibCompressDynamicParallel_eq
    (raw : ByteArray) (parallel : PngParallelOptions) :
    Png.zlibCompressDynamicParallel raw parallel = Png.zlibCompressDynamic raw := by
  simp [Png.zlibCompressDynamicParallel, Png.zlibCompressDynamic]

/-- Parallel IDAT compression is equal to the sequential mode-specific
compressor. Each mode preserves the exact zlib bytes of the existing encoder. -/
@[simp] lemma compressIdatParallel_eq
    (mode : PngEncodeMode) (raw : ByteArray) (parallel : PngParallelOptions) :
    Png.compressIdatParallel mode raw parallel =
      match mode with
      | .stored => Png.zlibCompressStored raw
      | .fixed => Png.zlibCompressFixed raw
      | .dynamic => Png.zlibCompressDynamic raw := by
  cases mode <;> simp [Png.compressIdatParallel]

/-- Parallel chunk construction preserves the exact PNG chunk bytes. -/
@[simp] lemma mkChunkBytesParallel_eq
    (typBytes data : ByteArray) (parallel : PngParallelOptions) :
    Png.mkChunkBytesParallel typBytes data parallel =
      Png.mkChunkBytes typBytes data := by
  unfold Png.mkChunkBytesParallel Png.mkChunkBytes
  split <;> rfl

/-- Parallel construction of IHDR/IDAT/IEND chunks preserves the exact envelope
used by the sequential encoder core. -/
@[simp] lemma encodeBitmapChunksParallel_eq
    (ihdr ancillary idat : ByteArray) (parallel : PngParallelOptions) :
    Png.encodeBitmapChunksParallel ihdr ancillary idat parallel =
      (let ihdrChunk := Png.mkChunkBytes Png.ihdrTypeBytes ihdr
       let idatChunk := Png.mkChunkBytes Png.idatTypeBytes idat
       let iendChunk := Png.mkChunkBytes Png.iendTypeBytes ByteArray.empty
       let outSize := Png.pngSignature.size + ihdrChunk.size + ancillary.size +
         idatChunk.size + iendChunk.size
       let out := ByteArray.emptyWithCapacity outSize
       out ++ Png.pngSignature ++ ihdrChunk ++ ancillary ++ idatChunk ++ iendChunk) := by
  unfold Png.encodeBitmapChunksParallel
  split <;> rfl

/-- The parallel option-aware encoder core is byte-for-byte equal to the
existing sequential encoder core. -/
@[simp] lemma encodeBitmapCoreParallel_eq
    (raw ihdr : ByteArray) (mode : PngEncodeMode)
    (colorSpace : Option PngEncodeColorSpace) (chromaticities : Option PngChromaticities)
    (physical : Option PngPhysicalPixelDimensions)
    (modificationTime : Option PngTime)
    (parallel : PngParallelOptions) :
    Png.encodeBitmapCoreParallel raw ihdr mode colorSpace chromaticities
        physical modificationTime parallel =
      Png.encodeBitmapCore raw ihdr mode colorSpace chromaticities
        physical modificationTime := by
  simp [Png.encodeBitmapCoreParallel, Png.encodeBitmapCore]
  rfl

/-- Parallel bitmap encoding is byte-for-byte equal to the existing encoder. -/
@[simp] lemma encodeBitmapParallel_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode) (parallel : PngParallelOptions) :
    Png.encodeBitmapParallel (px := px) bmp hw hh mode parallel =
      Png.encodeBitmap (px := px) bmp hw hh mode := by
  cases mode <;>
    simp [Png.encodeBitmapParallel, Png.encodeBitmap, Png.compressIdatParallel, Id.run]

/-- One-shard segmented fixed-Huffman bitmap encoding is byte-for-byte equal to
the existing fixed-Huffman bitmap encoder. Multi-shard mode keeps only semantic
round-trip compatibility because LZ77 matches are shard-local. -/
@[simp] lemma encodeBitmapFixedSegmentedParallel_oneShard_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size) :
    Png.encodeBitmapFixedSegmentedParallel (px := px) bmp hw hh
        oneShardPngParallelOptions =
      Png.encodeBitmap (px := px) bmp hw hh .fixed := by
  simp [Png.encodeBitmapFixedSegmentedParallel, Png.encodeBitmap, Id.run]

/-- Parallel option-aware bitmap encoding is equal to the existing encoder. -/
@[simp] lemma encodeBitmapWithOptionsParallel_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (options : PngEncodeOptions) (parallel : PngParallelOptions) :
    Png.encodeBitmapWithOptionsParallel (px := px) bmp hw hh options parallel =
      Png.encodeBitmapWithOptions (px := px) bmp hw hh options := by
  simp [Png.encodeBitmapWithOptionsParallel, Png.encodeBitmapWithOptions]
  rfl

/-- Parallel checked bitmap encoding preserves the checked encoder result. -/
@[simp] lemma encodeBitmapCheckedParallel_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (mode : PngEncodeMode) (parallel : PngParallelOptions) :
    Png.encodeBitmapCheckedParallel (px := px) bmp mode parallel =
      Png.encodeBitmapChecked (px := px) bmp mode := by
  unfold Png.encodeBitmapCheckedParallel Png.encodeBitmapChecked
  by_cases hw : bmp.size.width < UInt32.size
  · by_cases hh : bmp.size.height < UInt32.size <;> simp [hw, hh]
  · simp [hw]

/-- One-shard segmented fixed-Huffman checked bitmap encoding preserves the
existing checked fixed-Huffman encoder result. -/
@[simp] lemma encodeBitmapFixedSegmentedCheckedParallel_oneShard_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) :
    Png.encodeBitmapFixedSegmentedCheckedParallel (px := px) bmp
        oneShardPngParallelOptions =
      Png.encodeBitmapChecked (px := px) bmp .fixed := by
  unfold Png.encodeBitmapFixedSegmentedCheckedParallel Png.encodeBitmapChecked
  by_cases hw : bmp.size.width < UInt32.size
  · by_cases hh : bmp.size.height < UInt32.size <;> simp [hw, hh]
  · simp [hw]

/-- Parallel checked option-aware bitmap encoding preserves the checked result. -/
@[simp] lemma encodeBitmapWithOptionsCheckedParallel_eq {px : Type u}
    [PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (options : PngEncodeOptions) (parallel : PngParallelOptions) :
    Png.encodeBitmapWithOptionsCheckedParallel (px := px) bmp options parallel =
      Png.encodeBitmapWithOptionsChecked (px := px) bmp options := by
  unfold Png.encodeBitmapWithOptionsCheckedParallel Png.encodeBitmapWithOptionsChecked
  by_cases hw : bmp.size.width < UInt32.size
  · by_cases hh : bmp.size.height < UInt32.size
    · simp [hw, hh]
      rfl
    · simp [hw, hh]
  · simp [hw]

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
  unfold Png.decodeBitmapWithMetadataParallel Png.decodeBitmapWithMetadata
  by_cases h : 8 <= bytes.size <;> simp [h]

/-- Parallel Gray1 encoding is byte-for-byte equal to the existing encoder. -/
@[simp] lemma encodeGray1BitmapParallel_eq
    (bmp : Bitmap.Gray1)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode) (parallel : PngParallelOptions) :
    Png.encodeGray1BitmapParallel bmp hw hh mode parallel =
      Png.encodeGray1Bitmap bmp hw hh mode := by
  cases mode <;> simp [Png.encodeGray1BitmapParallel, Png.encodeGray1Bitmap,
    Png.compressIdatParallel, Id.run]

/-- Parallel option-aware Gray1 encoding is equal to the existing encoder. -/
@[simp] lemma encodeGray1BitmapWithOptionsParallel_eq
    (bmp : Bitmap.Gray1)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (options : PngEncodeOptions) (parallel : PngParallelOptions) :
  Png.encodeGray1BitmapWithOptionsParallel bmp hw hh options parallel =
      Png.encodeGray1BitmapWithOptions bmp hw hh options := by
  simp [Png.encodeGray1BitmapWithOptionsParallel, Png.encodeGray1BitmapWithOptions]

/-- Parallel checked Gray1 encoding preserves the existing checked result. -/
@[simp] lemma encodeGray1BitmapCheckedParallel_eq
    (bmp : Bitmap.Gray1) (mode : PngEncodeMode) (parallel : PngParallelOptions) :
    Png.encodeGray1BitmapCheckedParallel bmp mode parallel =
      Png.encodeGray1BitmapChecked bmp mode := by
  unfold Png.encodeGray1BitmapCheckedParallel Png.encodeGray1BitmapChecked
  by_cases hw : bmp.size.width < UInt32.size
  · by_cases hh : bmp.size.height < UInt32.size <;> simp [hw, hh]
  · simp [hw]

/-- Parallel checked option-aware Gray1 encoding preserves the checked result. -/
@[simp] lemma encodeGray1BitmapWithOptionsCheckedParallel_eq
    (bmp : Bitmap.Gray1) (options : PngEncodeOptions) (parallel : PngParallelOptions) :
    Png.encodeGray1BitmapWithOptionsCheckedParallel bmp options parallel =
      Png.encodeGray1BitmapWithOptionsChecked bmp options := by
  unfold Png.encodeGray1BitmapWithOptionsCheckedParallel
    Png.encodeGray1BitmapWithOptionsChecked
  by_cases hw : bmp.size.width < UInt32.size
  · by_cases hh : bmp.size.height < UInt32.size
    · simp [hw, hh]
      rfl
    · simp [hw, hh]
  · simp [hw]

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
  cases options.mode <;>
    simp [Png.encodeIndexedBitmapWithOptionsParallel, Png.encodeIndexedBitmapWithOptions,
      Png.compressIdatParallel, ByteArray.append_assoc] <;> rfl

/-- Parallel checked indexed encoding preserves the existing checked result. -/
@[simp] lemma encodeIndexedBitmapWithOptionsCheckedParallel_eq
    (bmp : PngIndexedBitmap) (options : PngEncodeOptions)
    (parallel : PngParallelOptions) :
    Png.encodeIndexedBitmapWithOptionsCheckedParallel bmp options parallel =
      Png.encodeIndexedBitmapWithOptionsChecked bmp options := by
  unfold Png.encodeIndexedBitmapWithOptionsCheckedParallel
    Png.encodeIndexedBitmapWithOptionsChecked
  simp
  rfl

/-- Parallel checked indexed encoding by mode preserves the existing result. -/
@[simp] lemma encodeIndexedBitmapCheckedParallel_eq
    (bmp : PngIndexedBitmap) (mode : PngEncodeMode)
    (parallel : PngParallelOptions) :
    Png.encodeIndexedBitmapCheckedParallel bmp mode parallel =
      Png.encodeIndexedBitmapChecked bmp mode := by
  simp [Png.encodeIndexedBitmapCheckedParallel, Png.encodeIndexedBitmapChecked]

/-- Parallel indexed metadata-aware decoding preserves the existing result. -/
@[simp] lemma decodeIndexedBitmapWithMetadataParallel_eq
    (bytes : ByteArray) (parallel : PngParallelOptions) :
  Png.decodeIndexedBitmapWithMetadataParallel bytes parallel =
      Png.decodeIndexedBitmapWithMetadata bytes := by
  unfold Png.decodeIndexedBitmapWithMetadataParallel Png.decodeIndexedBitmapWithMetadata
  by_cases h : 8 <= bytes.size <;> simp [h]

/-- Parallel indexed decoding preserves the existing result. -/
@[simp] lemma decodeIndexedBitmapParallel_eq
    (bytes : ByteArray) (parallel : PngParallelOptions) :
    Png.decodeIndexedBitmapParallel bytes parallel =
      Png.decodeIndexedBitmap bytes := by
  simp [Png.decodeIndexedBitmapParallel, Png.decodeIndexedBitmap]

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

/-- One-shard segmented fixed-Huffman encode plus parallel decode round trips by
reducing to the established sequential fixed-Huffman round-trip theorem. -/
lemma decodeBitmapParallel_encodeBitmapFixedSegmentedParallel_oneShard {px : Type u}
    [PixelFormat px] [Png.PixelFormat px] [PngRoundTrip px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (parallelDecode : PngParallelOptions)
    (hidat : (encodeBitmapIdat (bmp := bmp) (mode := .fixed)).size < 2 ^ 32) :
    Png.decodeBitmapParallel (px := px)
        (Png.encodeBitmapFixedSegmentedParallel (px := px) bmp hw hh
          oneShardPngParallelOptions)
        parallelDecode =
      some bmp := by
  rw [decodeBitmapParallel_eq, encodeBitmapFixedSegmentedParallel_oneShard_eq]
  exact decodeBitmap_encodeBitmap (bmp := bmp)
    (hw := by simpa [UInt32.size] using hw)
    (hh := by simpa [UInt32.size] using hh)
    (mode := .fixed) hidat

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
