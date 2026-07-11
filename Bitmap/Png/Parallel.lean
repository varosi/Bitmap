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

def encodeBitmapParallel {px : Type u} [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode := .fixed) (parallel : PngParallelOptions := {}) : ByteArray :=
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeBitmap (px := px) bmp hw hh mode

def encodeBitmapWithOptionsParallel {px : Type u} [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (options : PngEncodeOptions := {}) (parallel : PngParallelOptions := {}) :
    Option ByteArray :=
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeBitmapWithOptions (px := px) bmp hw hh options

def encodeBitmapCheckedParallel {px : Type u} [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (mode : PngEncodeMode := .fixed)
    (parallel : PngParallelOptions := {}) : Except String ByteArray :=
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeBitmapChecked (px := px) bmp mode

def encodeBitmapWithOptionsCheckedParallel {px : Type u}
    [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (options : PngEncodeOptions := {})
    (parallel : PngParallelOptions := {}) : Except String ByteArray :=
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeBitmapWithOptionsChecked (px := px) bmp options

def decodeBitmapParallel {px : Type u} [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bytes : ByteArray) (parallel : PngParallelOptions := {}) : Option (Bitmap px) :=
  parallelEval parallel bytes.size bytes.size fun _ =>
    decodeBitmap (px := px) bytes

def decodeBitmapWithMetadataParallel {px : Type u}
    [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bytes : ByteArray) (parallel : PngParallelOptions := {}) :
    Option (PngDecodeResult px) :=
  parallelEval parallel bytes.size bytes.size fun _ =>
    decodeBitmapWithMetadata (px := px) bytes

def encodeGray1BitmapParallel (bmp : Bitmap.Gray1)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode := .fixed) (parallel : PngParallelOptions := {}) :
    ByteArray :=
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeGray1Bitmap bmp hw hh mode

def encodeGray1BitmapWithOptionsParallel (bmp : Bitmap.Gray1)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (options : PngEncodeOptions := {}) (parallel : PngParallelOptions := {}) :
    Option ByteArray :=
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeGray1BitmapWithOptions bmp hw hh options

def encodeGray1BitmapCheckedParallel (bmp : Bitmap.Gray1)
    (mode : PngEncodeMode := .fixed) (parallel : PngParallelOptions := {}) :
    Except String ByteArray :=
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeGray1BitmapChecked bmp mode

def encodeGray1BitmapWithOptionsCheckedParallel (bmp : Bitmap.Gray1)
    (options : PngEncodeOptions := {}) (parallel : PngParallelOptions := {}) :
    Except String ByteArray :=
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeGray1BitmapWithOptionsChecked bmp options

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
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeIndexedBitmapWithOptions bmp options

def encodeIndexedBitmapWithOptionsCheckedParallel (bmp : PngIndexedBitmap)
    (options : PngEncodeOptions := {}) (parallel : PngParallelOptions := {}) :
    Except String ByteArray :=
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeIndexedBitmapWithOptionsChecked bmp options

def encodeIndexedBitmapCheckedParallel (bmp : PngIndexedBitmap)
    (mode : PngEncodeMode := .fixed) (parallel : PngParallelOptions := {}) :
    Except String ByteArray :=
  parallelEval parallel bmp.size.height bmp.data.size fun _ =>
    encodeIndexedBitmapChecked bmp mode

def decodeIndexedBitmapWithMetadataParallel (bytes : ByteArray)
    (parallel : PngParallelOptions := {}) : Option PngIndexedDecodeResult :=
  parallelEval parallel bytes.size bytes.size fun _ =>
    decodeIndexedBitmapWithMetadata bytes

def decodeIndexedBitmapParallel (bytes : ByteArray)
    (parallel : PngParallelOptions := {}) : Option PngIndexedBitmap :=
  parallelEval parallel bytes.size bytes.size fun _ =>
    decodeIndexedBitmap bytes

end Png
end Bitmaps
