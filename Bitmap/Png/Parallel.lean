import Bitmap.Png

universe u

namespace Bitmaps
namespace Png

/-!
  Parallel PNG entry points and deterministic scheduling helpers.

  The public functions in this module preserve the existing pure PNG API surface:
  they evaluate the same sequential implementation under Lean tasks when the
  configured work-size thresholds say the input is large enough. The explicit
  shard helpers are kept separate so future measured hotspots can move from
  whole-call tasks to finer row or byte-range tasks without changing callers.
-/

/-- Options for PNG parallel execution. Shard counts are derived from input
work size and these explicit thresholds; no local CPU/core-count query is used. -/
structure PngParallelOptions where
  maxShards : Nat := 256
  minRowsPerShard : Nat := 16
  targetBytesPerShard : Nat := 262144
deriving Repr, DecidableEq

/-- A half-open work range `[start, stop)` used by deterministic shard helpers. -/
structure PngShard where
  start : Nat
  stop : Nat
deriving Repr, DecidableEq

/-- Size of a half-open shard range. Empty or inverted ranges report zero work. -/
def PngShard.size (shard : PngShard) : Nat :=
  shard.stop - shard.start

/-- Ceiling division for scheduler thresholds. A zero divisor is treated as a
request for no division so option normalization remains total. -/
def parallelCeilDiv (n d : Nat) : Nat :=
  if d = 0 then n else (n + d - 1) / d

/-- Normalize `maxShards` so every scheduler call has at least one shard. -/
def PngParallelOptions.normalizedMaxShards (options : PngParallelOptions) : Nat :=
  Nat.max 1 options.maxShards

/-- Choose a deterministic shard count from units and bytes of work. This is
intentionally independent of the executing machine's core count. -/
def PngParallelOptions.shardCountForWork
    (options : PngParallelOptions) (workUnits workBytes : Nat) : Nat :=
  let maxShards := options.normalizedMaxShards
  let rowShards := parallelCeilDiv workUnits options.minRowsPerShard
  let byteShards := parallelCeilDiv workBytes options.targetBytesPerShard
  Nat.max 1 (Nat.min maxShards (Nat.max rowShards byteShards))

/-- Whether an input is large enough to use a task instead of direct evaluation. -/
def PngParallelOptions.useParallel
    (options : PngParallelOptions) (workUnits workBytes : Nat) : Bool :=
  options.shardCountForWork workUnits workBytes > 1

/-- Split `total` work units into deterministic, ordered, half-open ranges. -/
def shardRanges (total shardCount : Nat) : List PngShard :=
  if shardCount = 0 then
    []
  else
    (List.range shardCount).map fun i =>
      { start := (i * total) / shardCount
        stop := ((i + 1) * total) / shardCount }

/-- Row-oriented shard ranges for a row-byte workload. -/
def rowShardRanges (options : PngParallelOptions) (rows rowBytes : Nat) : List PngShard :=
  shardRanges rows (options.shardCountForWork rows (rows * (rowBytes + 1)))

/-- Byte-oriented shard ranges. -/
def byteShardRanges (options : PngParallelOptions) (bytes : Nat) : List PngShard :=
  shardRanges bytes (options.shardCountForWork bytes bytes)

/-- Run one deterministic pure task per shard and return results in shard order. -/
def mapShardsParallel {α : Type u} (shards : List PngShard) (f : PngShard → α) : List α :=
  let tasks := shards.map fun shard => Task.spawn (fun _ => f shard)
  tasks.map fun task => task.get

/-- Evaluate deterministic pure work directly or through a task according to
the configured work-size thresholds. -/
def parallelEval {α : Type u}
    (options : PngParallelOptions) (workUnits workBytes : Nat) (f : Unit → α) : α :=
  if options.useParallel workUnits workBytes then
    (Task.spawn f).get
  else
    f ()

/-- Build a zlib stream with independent tasks for the deflated payload and
Adler checksum when the configured thresholds allow parallel work. -/
def zlibCompressWithParallel
    (deflate : ByteArray → ByteArray) (raw : ByteArray)
    (parallel : PngParallelOptions := {}) : ByteArray :=
  if parallel.useParallel 2 raw.size then
    let header := ByteArray.mk #[u8 0x78, u8 0x01]
    let deflatedTask := Task.spawn fun _ => deflate raw
    let adlerTask := Task.spawn fun _ => u32be (adler32 raw).toNat
    let deflated := deflatedTask.get
    let adler := adlerTask.get
    let outSize := header.size + deflated.size + adler.size
    let out := ByteArray.emptyWithCapacity outSize
    out ++ header ++ deflated ++ adler
  else
    let header := ByteArray.mk #[u8 0x78, u8 0x01]
    let deflated := deflate raw
    let adler := u32be (adler32 raw).toNat
    let outSize := header.size + deflated.size + adler.size
    let out := ByteArray.emptyWithCapacity outSize
    out ++ header ++ deflated ++ adler

/-- Build a stored zlib stream with independent tasks for the stored deflate
payload and Adler checksum when the configured thresholds allow parallel work. -/
def zlibCompressStoredParallel
    (raw : ByteArray) (parallel : PngParallelOptions := {}) : ByteArray :=
  zlibCompressWithParallel deflateStored raw parallel

/-- Build a fixed-Huffman zlib stream with independent tasks for deflate and
Adler checksum. The fixed bitstream itself remains sequential and unchanged. -/
def zlibCompressFixedParallel
    (raw : ByteArray) (parallel : PngParallelOptions := {}) : ByteArray :=
  zlibCompressWithParallel deflateFixed raw parallel

/-- Build a dynamic-Huffman zlib stream with independent tasks for deflate and
Adler checksum. The dynamic bitstream itself remains sequential and unchanged. -/
def zlibCompressDynamicParallel
    (raw : ByteArray) (parallel : PngParallelOptions := {}) : ByteArray :=
  zlibCompressWithParallel deflateDynamic raw parallel

/-- Compress IDAT payloads. Each zlib wrapper can compute the deflated payload
and Adler checksum independently; the deflate bitstream algorithms themselves
remain byte-for-byte unchanged. -/
def compressIdatParallel
    (mode : PngEncodeMode) (raw : ByteArray) (parallel : PngParallelOptions := {}) :
    ByteArray :=
  match mode with
  | .stored => zlibCompressStoredParallel raw parallel
  | .fixed => zlibCompressFixedParallel raw parallel
  | .dynamic => zlibCompressDynamicParallel raw parallel

/-- Construct a PNG chunk while computing the CRC in a task when useful. -/
def mkChunkBytesParallel
    (typBytes : ByteArray) (data : ByteArray) (parallel : PngParallelOptions := {}) :
    ByteArray :=
  if parallel.useParallel 1 (typBytes.size + data.size) then
    let lenBytes := u32be data.size
    let crcTask := Task.spawn fun _ => crc32Chunk typBytes data
    let crc := crcTask.get
    let outSize := lenBytes.size + typBytes.size + data.size + 4
    let out := ByteArray.emptyWithCapacity outSize
    out ++ lenBytes ++ typBytes ++ data ++ u32be crc.toNat
  else
    mkChunkBytes typBytes data

/-- Build the fixed PNG chunk envelope with independent IHDR, IDAT, and IEND
chunk construction tasks while preserving deterministic output order. -/
def encodeBitmapChunksParallel
    (ihdr ancillary idat : ByteArray) (parallel : PngParallelOptions := {}) :
    ByteArray :=
  if parallel.useParallel 3 (ihdr.size + ancillary.size + idat.size) then
    let ihdrTask := Task.spawn fun _ => mkChunkBytes ihdrTypeBytes ihdr
    let idatTask := Task.spawn fun _ => mkChunkBytes idatTypeBytes idat
    let iendTask := Task.spawn fun _ => mkChunkBytes iendTypeBytes ByteArray.empty
    let ihdrChunk := ihdrTask.get
    let idatChunk := idatTask.get
    let iendChunk := iendTask.get
    let outSize := pngSignature.size + ihdrChunk.size + ancillary.size +
      idatChunk.size + iendChunk.size
    let out := ByteArray.emptyWithCapacity outSize
    out ++ pngSignature ++ ihdrChunk ++ ancillary ++ idatChunk ++ iendChunk
  else
    let ihdrChunk := mkChunkBytes ihdrTypeBytes ihdr
    let idatChunk := mkChunkBytes idatTypeBytes idat
    let iendChunk := mkChunkBytes iendTypeBytes ByteArray.empty
    let outSize := pngSignature.size + ihdrChunk.size + ancillary.size +
      idatChunk.size + iendChunk.size
    let out := ByteArray.emptyWithCapacity outSize
    out ++ pngSignature ++ ihdrChunk ++ ancillary ++ idatChunk ++ iendChunk

/-- Option-aware encoder core used by the public parallel bitmap APIs. -/
def encodeBitmapCoreParallel (raw ihdr : ByteArray) (mode : PngEncodeMode)
    (colorSpace : Option PngEncodeColorSpace) (chromaticities : Option PngChromaticities)
    (physical : Option PngPhysicalPixelDimensions)
    (modificationTime : Option PngTime)
    (parallel : PngParallelOptions := {}) : Option ByteArray := do
  let ancillary ← encodeAncillaryChunks? colorSpace chromaticities physical modificationTime
  let idat := compressIdatParallel mode raw parallel
  some (encodeBitmapChunksParallel ihdr ancillary idat parallel)

def encodeBitmapParallel {px : Type u} [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode := .fixed) (parallel : PngParallelOptions := {}) : ByteArray :=
  have _ := hw
  have _ := hh
  let raw := Png.PixelFormat.encodeRaw (α := px) bmp
  let ihdr := u32be bmp.size.width ++ u32be bmp.size.height ++
    ByteArray.mk #[Png.PixelFormat.bitDepth (α := px), Png.PixelFormat.colorType (α := px),
      u8 0, u8 0, u8 0]
  let idat := compressIdatParallel mode raw parallel
  encodeBitmapChunksParallel ihdr ByteArray.empty idat parallel

def encodeBitmapWithOptionsParallel {px : Type u} [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (options : PngEncodeOptions := {}) (parallel : PngParallelOptions := {}) :
    Option ByteArray :=
  have _ := hw
  have _ := hh
  let raw :=
    match options.filter with
    | .none => Png.PixelFormat.encodeRaw (α := px) bmp
    | _ => encodeRawWithFilter bmp options.filter
  let ihdr := u32be bmp.size.width ++ u32be bmp.size.height ++
    ByteArray.mk #[Png.PixelFormat.bitDepth (α := px), Png.PixelFormat.colorType (α := px),
      u8 0, u8 0, u8 0]
  encodeBitmapCoreParallel raw ihdr options.mode options.colorSpace options.chromaticities
    options.physical options.modificationTime parallel

def encodeBitmapCheckedParallel {px : Type u} [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (mode : PngEncodeMode := .fixed)
    (parallel : PngParallelOptions := {}) : Except String ByteArray :=
  if hw : bmp.size.width < UInt32.size then
    if hh : bmp.size.height < UInt32.size then
      Except.ok (encodeBitmapParallel (px := px) bmp hw hh mode parallel)
    else
      Except.error "bitmap height exceeds PNG limit (2^32)"
  else
    Except.error "bitmap width exceeds PNG limit (2^32)"

def encodeBitmapWithOptionsCheckedParallel {px : Type u}
    [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (options : PngEncodeOptions := {})
    (parallel : PngParallelOptions := {}) : Except String ByteArray :=
  if hw : bmp.size.width < UInt32.size then
    if hh : bmp.size.height < UInt32.size then
      match encodeBitmapWithOptionsParallel (px := px) bmp hw hh options parallel with
      | some bytes => Except.ok bytes
      | none => Except.error "invalid PNG ancillary encode options"
    else
      Except.error "bitmap height exceeds PNG limit (2^32)"
  else
    Except.error "bitmap width exceeds PNG limit (2^32)"

def decodeBitmapParallel {px : Type u} [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bytes : ByteArray) (parallel : PngParallelOptions := {}) : Option (Bitmap px) :=
  parallelEval parallel bytes.size bytes.size fun _ =>
    decodeBitmap (px := px) bytes

def decodeBitmapWithMetadataParallel {px : Type u}
    [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bytes : ByteArray) (parallel : PngParallelOptions := {}) :
    Option (PngDecodeResult px) :=
  do
  let parsed ←
    if hsize : 8 <= bytes.size then
      parsePngWithMetadata bytes hsize
    else
      none
  parallelEval parallel parsed.header.height parsed.idat.size fun _ =>
    decodeParsedBitmapWithMetadata (px := px) parsed

def encodeGray1BitmapParallel (bmp : Bitmap.Gray1)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode := .fixed) (parallel : PngParallelOptions := {}) :
    ByteArray :=
  have _ := hw
  have _ := hh
  let raw := encodeRawGray1 bmp
  let ihdr := u32be bmp.size.width ++ u32be bmp.size.height ++
    ByteArray.mk #[u8 1, u8 0, u8 0, u8 0, u8 0]
  let idat := compressIdatParallel mode raw parallel
  encodeBitmapChunksParallel ihdr ByteArray.empty idat parallel

def encodeGray1BitmapWithOptionsParallel (bmp : Bitmap.Gray1)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (options : PngEncodeOptions := {}) (parallel : PngParallelOptions := {}) :
    Option ByteArray :=
  have _ := hw
  have _ := hh
  let raw := encodeRawGray1WithFilter bmp options.filter
  let ihdr := u32be bmp.size.width ++ u32be bmp.size.height ++
    ByteArray.mk #[u8 1, u8 0, u8 0, u8 0, u8 0]
  encodeBitmapCoreParallel raw ihdr options.mode options.colorSpace options.chromaticities
    options.physical options.modificationTime parallel

def encodeGray1BitmapCheckedParallel (bmp : Bitmap.Gray1)
    (mode : PngEncodeMode := .fixed) (parallel : PngParallelOptions := {}) :
    Except String ByteArray :=
  if hw : bmp.size.width < UInt32.size then
    if hh : bmp.size.height < UInt32.size then
      Except.ok (encodeGray1BitmapParallel bmp hw hh mode parallel)
    else
      Except.error "bitmap height exceeds PNG limit (2^32)"
  else
    Except.error "bitmap width exceeds PNG limit (2^32)"

def encodeGray1BitmapWithOptionsCheckedParallel (bmp : Bitmap.Gray1)
    (options : PngEncodeOptions := {}) (parallel : PngParallelOptions := {}) :
    Except String ByteArray :=
  if hw : bmp.size.width < UInt32.size then
    if hh : bmp.size.height < UInt32.size then
      match encodeGray1BitmapWithOptionsParallel bmp hw hh options parallel with
      | some bytes => Except.ok bytes
      | none => Except.error "invalid PNG ancillary encode options"
    else
      Except.error "bitmap height exceeds PNG limit (2^32)"
  else
    Except.error "bitmap width exceeds PNG limit (2^32)"

def decodeGray1BitmapParallel (bytes : ByteArray)
    (parallel : PngParallelOptions := {}) : Option Bitmap.Gray1 :=
  parallelEval parallel bytes.size bytes.size fun _ =>
    decodeGray1Bitmap bytes

def decodeGray1BitmapWithMetadataParallel (bytes : ByteArray)
    (parallel : PngParallelOptions := {}) : Option PngDecodeGray1Result :=
  parallelEval parallel bytes.size bytes.size fun _ =>
    decodeGray1BitmapWithMetadata bytes

def encodeIndexedBitmapWithOptionsParallel (bmp : PngIndexedBitmap)
    (options : PngEncodeOptions := {}) (parallel : PngParallelOptions := {}) :
    Option ByteArray :=
  do
  let colorSpaceChunks ← encodeColorSpaceChunks? options.colorSpace options.chromaticities
  let physChunk ← encodePhysChunk? options.physical
  let timeChunk ← encodeTimeChunk? options.modificationTime
  let raw := encodeRawIndexedWithFilter bmp options.filter
  let idat := compressIdatParallel options.mode raw parallel
  let ihdr := u32be bmp.size.width ++ u32be bmp.size.height ++
    ByteArray.mk #[u8 bmp.bitDepth, u8 3, u8 0, u8 0, u8 0]
  let plteTask := Task.spawn fun _ => mkChunkBytes plteTypeBytes bmp.palette.entries
  let trnsTask := Task.spawn fun _ =>
    match bmp.transparency with
    | some alpha => mkChunkBytes trnsTypeBytes alpha
    | none => ByteArray.empty
  let bkgdTask := Task.spawn fun _ =>
    match bmp.background with
    | some idx => mkChunkBytes bkgdTypeBytes (ByteArray.mk #[idx])
    | none => ByteArray.empty
  let ihdrChunk := mkChunkBytesParallel ihdrTypeBytes ihdr parallel
  let plteChunk := plteTask.get
  let trnsChunk := trnsTask.get
  let bkgdChunk := bkgdTask.get
  let idatChunk := mkChunkBytesParallel idatTypeBytes idat parallel
  let iendChunk := mkChunkBytesParallel iendTypeBytes ByteArray.empty parallel
  let outSize := pngSignature.size + ihdrChunk.size + colorSpaceChunks.size +
    plteChunk.size + trnsChunk.size + bkgdChunk.size + physChunk.size +
    timeChunk.size + idatChunk.size + iendChunk.size
  let out := ByteArray.emptyWithCapacity outSize
  some (out ++ pngSignature ++ ihdrChunk ++ colorSpaceChunks ++ plteChunk ++
    trnsChunk ++ bkgdChunk ++ physChunk ++ timeChunk ++ idatChunk ++ iendChunk)

def encodeIndexedBitmapWithOptionsCheckedParallel (bmp : PngIndexedBitmap)
    (options : PngEncodeOptions := {}) (parallel : PngParallelOptions := {}) :
    Except String ByteArray :=
  do
  validateIndexedBitmap bmp
  match encodeIndexedBitmapWithOptionsParallel bmp options parallel with
  | some bytes => Except.ok bytes
  | none => Except.error "invalid PNG ancillary encode options"

def encodeIndexedBitmapCheckedParallel (bmp : PngIndexedBitmap)
    (mode : PngEncodeMode := .fixed) (parallel : PngParallelOptions := {}) :
    Except String ByteArray :=
  encodeIndexedBitmapWithOptionsCheckedParallel bmp { mode := mode } parallel

def decodeIndexedBitmapWithMetadataParallel (bytes : ByteArray)
    (parallel : PngParallelOptions := {}) : Option PngIndexedDecodeResult :=
  do
  let parsed ←
    if hsize : 8 <= bytes.size then
      parsePngWithMetadata bytes hsize
    else
      none
  parallelEval parallel parsed.header.height parsed.idat.size fun _ =>
    decodeParsedIndexedBitmapWithMetadata parsed

def decodeIndexedBitmapParallel (bytes : ByteArray)
    (parallel : PngParallelOptions := {}) : Option PngIndexedBitmap :=
  do
  let parsed ←
    if hsize : 8 <= bytes.size then
      parsePngForDecode bytes hsize
    else
      none
  parallelEval parallel parsed.header.height parsed.idat.size fun _ => do
    if parsed.metadata.transparency.isSome then
      none
    let parsed :=
      { parsed with metadata := PngMetadata.pixelOnlyColorSpace parsed.metadata }
    let decoded ← decodeParsedIndexedBitmapWithMetadata parsed
    some decoded.bitmap

end Png
end Bitmaps
