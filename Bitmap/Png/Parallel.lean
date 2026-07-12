import Bitmap.Png

universe u v

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

/-- Run one deterministic pure task per list element and return results in list order. -/
def mapListParallel {α : Type u} {β : Type v} (xs : List α) (f : α → β) : List β :=
  let tasks := xs.map fun x => Task.spawn (fun _ => f x)
  tasks.map fun task => task.get

/-- Extract the work items covered by a shard of list indices. -/
def listShard {α : Type u} (xs : List α) (shard : PngShard) : List α :=
  (xs.drop shard.start).take shard.size

/-- Evaluate deterministic pure work directly or through a task according to
the configured work-size thresholds. -/
def parallelEval {α : Type u}
    (options : PngParallelOptions) (workUnits workBytes : Nat) (f : Unit → α) : α :=
  if options.useParallel workUnits workBytes then
    (Task.spawn f).get
  else
    f ()

/-- Concatenate byte chunks in their existing order. -/
def concatByteArrays (chunks : List ByteArray) : ByteArray :=
  chunks.foldr (fun chunk out => chunk ++ out) ByteArray.empty

/-- Concatenate byte chunks after precomputing the output capacity. This is
used by large explicit stored-mode parallel helpers where concatenation cost is
part of the measured path and no proof depends on the fold shape. -/
def concatByteArraysWithCapacity (chunks : List ByteArray) : ByteArray :=
  let capacity := chunks.foldl (fun total chunk => total + chunk.size) 0
  Id.run do
    let mut out := ByteArray.emptyWithCapacity capacity
    for chunk in chunks do
      out := out ++ chunk
    return out

/-- Descriptor for a stored DEFLATE block payload inside the original raw
buffer. The final flag is stored explicitly because only the last block may set
it in the byte stream. -/
structure StoredDeflateBlockRange where
  start : Nat
  stop : Nat
  final : Bool
deriving Repr, DecidableEq

/-- Materialize a stored DEFLATE block descriptor from the original raw buffer. -/
def StoredDeflateBlockRange.toBlock
    (range : StoredDeflateBlockRange) (raw : ByteArray) : ByteArray :=
  storedBlock (raw.extract range.start range.stop) range.final

/-- Build stored DEFLATE block descriptors from an offset and remaining byte
count. This mirrors `deflateStored` without copying tail buffers. -/
def storedDeflateBlockRangesFrom
    (offset remaining : Nat) : List StoredDeflateBlockRange :=
  if _hzero : remaining = 0 then
    [{ start := offset, stop := offset, final := true }]
  else
    let blockLen := Nat.min uint16MaxValue remaining
    let stop := offset + blockLen
    if _hfinal : blockLen == remaining then
      [{ start := offset, stop := stop, final := true }]
    else
      { start := offset, stop := stop, final := false } ::
        storedDeflateBlockRangesFrom stop (remaining - blockLen)
termination_by remaining
decreasing_by
  have hle : blockLen ≤ remaining := by
    simpa [blockLen] using Nat.min_le_right uint16MaxValue remaining
  have hpos : 0 < blockLen := by
    have hpos_remaining : 0 < remaining := Nat.pos_of_ne_zero _hzero
    have hpos_max : 0 < uint16MaxValue := by
      simp [uint16MaxValue, UInt16.size]
    rw [Nat.lt_min]
    exact ⟨hpos_max, hpos_remaining⟩
  exact Nat.sub_lt_self hpos hle

/-- Stored DEFLATE block descriptors for the whole raw payload. -/
def storedDeflateBlockRanges (raw : ByteArray) : List StoredDeflateBlockRange :=
  storedDeflateBlockRangesFrom 0 raw.size

/-- Sequential stored-block construction through the range representation. -/
def deflateStoredByBlocks (raw : ByteArray) : ByteArray :=
  concatByteArrays <| (storedDeflateBlockRanges raw).map fun range =>
    range.toBlock raw

/-- Materialize a list of stored DEFLATE block descriptors in one shard. -/
def storedDeflateBlockRangeShardBytes
    (ranges : List StoredDeflateBlockRange) (raw : ByteArray) : ByteArray :=
  concatByteArraysWithCapacity <| ranges.map fun range => range.toBlock raw

/-- Build stored DEFLATE blocks in deterministic block-index shards. This keeps
the wire bytes identical to `deflateStored` while allowing block payload copies
and block headers to be prepared by independent tasks. -/
def deflateStoredParallel
    (raw : ByteArray) (parallel : PngParallelOptions := {}) : ByteArray :=
  let ranges := storedDeflateBlockRanges raw
  let blockCount := ranges.length
  if parallel.useParallel blockCount raw.size &&
      parallel.minRowsPerShard <= blockCount &&
      blockCount <= parallel.normalizedMaxShards then
    concatByteArrays <|
      mapListParallel ranges fun range =>
        range.toBlock raw
  else
    deflateStored raw

/-- Build stored DEFLATE blocks by grouping block descriptors into capped
block-index shards. Unlike `deflateStoredParallel`, this path still uses
parallel block construction when the stored-block count exceeds `maxShards`. -/
def deflateStoredGroupedParallel
    (raw : ByteArray) (parallel : PngParallelOptions := {}) : ByteArray :=
  let ranges := storedDeflateBlockRanges raw
  let blockCount := ranges.length
  if parallel.useParallel blockCount raw.size &&
      parallel.minRowsPerShard <= blockCount then
    let shards := shardRanges blockCount (parallel.shardCountForWork blockCount raw.size)
    concatByteArraysWithCapacity <|
      mapShardsParallel shards fun shard =>
        storedDeflateBlockRangeShardBytes (listShard ranges shard) raw
  else
    deflateStored raw

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
  zlibCompressWithParallel (fun raw => deflateStoredParallel raw parallel) raw parallel

/-- Stored zlib compression that keeps block construction parallel for large
payloads by grouping many stored blocks into each scheduled shard. -/
def zlibCompressStoredGroupedParallel
    (raw : ByteArray) (parallel : PngParallelOptions := {}) : ByteArray :=
  zlibCompressWithParallel (fun raw => deflateStoredGroupedParallel raw parallel) raw parallel

/-- Decode a stored-only zlib stream through the parallel scheduler. This keeps
the same validation and output bytes as `zlibDecompressStored` while exposing a
stored-specific parallel decode entry point. -/
def zlibDecompressStoredParallel
    (data : ByteArray) (hsize : 2 <= data.size)
    (parallel : PngParallelOptions := {}) : Option ByteArray :=
  parallelEval parallel data.size data.size fun _ =>
    zlibDecompressStored data hsize

/-! ### Stored-only zlib decode scanner

The public equality theorem for `zlibDecompressStoredParallel` keeps using the
existing decoder. The helpers below expose a scanner-based stored-only decode
path whose payload copies can be sharded and benchmarked independently. -/

/-- Payload range for one stored DEFLATE block inside a deflated byte stream. -/
structure StoredInflatePayloadRange where
  start : Nat
  stop : Nat
deriving Repr, DecidableEq

/-- Extract one stored payload range from the original deflated byte stream. -/
def StoredInflatePayloadRange.bytes
    (range : StoredInflatePayloadRange) (deflated : ByteArray) : ByteArray :=
  deflated.extract range.start range.stop

/-- Scan stored DEFLATE block descriptors from `offset`, returning the ordered
payload ranges and the byte position immediately after the final block. -/
def scanStoredInflatePayloadRangesFrom
    (deflated : ByteArray) (offset fuel : Nat) :
    Option (List StoredInflatePayloadRange × Nat) := do
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if hheader : offset < deflated.size then
        let header := deflated.get offset hheader
        let bfinal := header &&& (0x01 : UInt8)
        let btype := (header >>> 1) &&& (0x03 : UInt8)
        if btype != (0 : UInt8) then
          none
        else if hlen : offset + 4 < deflated.size then
          let len := readU16LE deflated (offset + 1) (by omega)
          let nlen := readU16LE deflated (offset + 3) (by omega)
          if len + nlen != uint16MaxValue then
            none
          else
            let start := offset + 5
            let stop := start + len
            if hbad : stop > deflated.size then
              none
            else
              let range : StoredInflatePayloadRange := { start, stop }
              if bfinal == (1 : UInt8) then
                some ([range], stop)
              else
                let (tail, rest) ←
                  scanStoredInflatePayloadRangesFrom deflated stop fuel
                some (range :: tail, rest)
        else
          none
      else
        none

/-- Scan a full stored DEFLATE stream and require the final stored block to end
exactly at the end of the stream. -/
def scanStoredInflatePayloadRanges
    (deflated : ByteArray) : Option (List StoredInflatePayloadRange) := do
  let (ranges, rest) ←
    scanStoredInflatePayloadRangesFrom deflated 0 (deflated.size + 1)
  if rest == deflated.size then
    some ranges
  else
    none

/-- Sequentially materialize stored payload ranges from a scanned stream. -/
def inflateStoredByPayloadRanges (deflated : ByteArray) : Option ByteArray := do
  let ranges ← scanStoredInflatePayloadRanges deflated
  some <| concatByteArrays <| ranges.map fun range => range.bytes deflated

/-- Materialize a shard of stored payload ranges from a scanned stream. -/
def storedInflatePayloadRangeShardBytes
    (ranges : List StoredInflatePayloadRange) (deflated : ByteArray) : ByteArray :=
  concatByteArraysWithCapacity <| ranges.map fun range => range.bytes deflated

/-- Decode a stored-only zlib stream by scanning block descriptors sequentially,
then extracting payload ranges through the parallel scheduler. This is intended
for large stored payloads where the old recursive inflater is copy-bound. -/
def zlibDecompressStoredScannedParallel
    (data : ByteArray) (hsize : 2 <= data.size)
    (parallel : PngParallelOptions := {}) : Option ByteArray := do
  let cmf := data.get 0 (by omega)
  let flg := data.get 1 (by omega)
  if ((cmf.toNat <<< 8) + flg.toNat) % 31 != 0 then
    none
  if (cmf &&& (0x0F : UInt8)) != (8 : UInt8) then
    none
  if (flg &&& (0x20 : UInt8)) != (0 : UInt8) then
    none
  if hmin : 6 ≤ data.size then
    let deflated := data.extract 2 (data.size - 4)
    let ranges ← scanStoredInflatePayloadRanges deflated
    let rangeCount := ranges.length
    let out :=
      if parallel.useParallel rangeCount deflated.size &&
          parallel.minRowsPerShard <= rangeCount then
        let shards := shardRanges rangeCount
          (parallel.shardCountForWork rangeCount deflated.size)
        concatByteArraysWithCapacity <|
          mapShardsParallel shards fun shard =>
            storedInflatePayloadRangeShardBytes (listShard ranges shard) deflated
      else
        concatByteArraysWithCapacity <| ranges.map fun range => range.bytes deflated
    let pos := data.size - 4
    have hAdler : pos + 3 < data.size := by
      have : 4 ≤ data.size := by omega
      omega
    let adlerExpected := readU32BE data pos hAdler
    let adlerActual := (adler32 out).toNat
    if adlerExpected != adlerActual then
      none
    return out
  else
    none

/-- Write one fixed-Huffman DEFLATE block from already-tokenized LZ77 data.
The writer is not flushed here so callers can concatenate multiple fixed blocks
in one bit stream and mark only the final block with `BFINAL = 1`. -/
def writeFixedLz77Block
    (bw : BitWriter) (tokens : Array Lz77Token) (final : Bool) : BitWriter :=
  let bw1 := bw.writeBits (if final then 1 else 0) 1
  let bw2 := bw1.writeBits 1 2
  let bw3 := writeFixedPayloadLz77 bw2 tokens
  let (eobCode, eobLen) := fixedLitLenCode 256
  bw3.writeBits (reverseBits eobCode eobLen) eobLen

/-- Tokenize one byte-range shard independently for segmented fixed-Huffman
DEFLATE. Independent tokenization avoids cross-shard LZ77 dependencies. -/
def fixedLz77ShardTokens (raw : ByteArray) (shard : PngShard) : Array Lz77Token :=
  deflateTokensLz77 (raw.extract shard.start shard.stop)

/-- Write an ordered list of fixed-Huffman LZ77 token chunks as independent
DEFLATE blocks. The empty-list case still emits a valid empty final block. -/
def writeFixedLz77Blocks : BitWriter → List (Array Lz77Token) → BitWriter
  | bw, [] => writeFixedLz77Block bw #[] true
  | bw, tokens :: [] => writeFixedLz77Block bw tokens true
  | bw, tokens :: next :: rest =>
      writeFixedLz77Blocks (writeFixedLz77Block bw tokens false) (next :: rest)

/-- Build a fixed-Huffman DEFLATE stream by tokenizing byte-range shards in
tasks and emitting one ordered fixed block per shard. This is semantically
equivalent after inflate, but not byte-for-byte equal to `deflateFixed` when
more than one shard is used because LZ77 matches intentionally do not cross
shard boundaries. -/
def deflateFixedSegmentedParallel
    (raw : ByteArray) (parallel : PngParallelOptions := {}) : ByteArray :=
  let shards := byteShardRanges parallel raw.size
  let tokenChunks :=
    if parallel.useParallel shards.length raw.size then
      mapShardsParallel shards (fixedLz77ShardTokens raw)
    else
      shards.map (fixedLz77ShardTokens raw)
  (writeFixedLz77Blocks BitWriter.empty tokenChunks).flush

/-- Build a fixed-Huffman zlib stream with independent tasks for deflate and
Adler checksum. The fixed bitstream itself remains sequential and unchanged. -/
def zlibCompressFixedParallel
    (raw : ByteArray) (parallel : PngParallelOptions := {}) : ByteArray :=
  zlibCompressWithParallel deflateFixed raw parallel

/-- Build a fixed-Huffman zlib stream whose DEFLATE payload is segmented into
ordered fixed blocks. This enables true shard-level tokenization parallelism
while preserving inflate semantics rather than exact compressed bytes. -/
def zlibCompressFixedSegmentedParallel
    (raw : ByteArray) (parallel : PngParallelOptions := {}) : ByteArray :=
  zlibCompressWithParallel (fun raw => deflateFixedSegmentedParallel raw parallel) raw parallel

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

/-- Encode a bitmap using the segmented fixed-Huffman parallel compressor.
This path preserves PNG round-trip semantics but may produce different IDAT
bytes from the sequential fixed encoder for multi-shard inputs. -/
def encodeBitmapFixedSegmentedParallel {px : Type u}
    [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (parallel : PngParallelOptions := {}) : ByteArray :=
  have _ := hw
  have _ := hh
  let raw := Png.PixelFormat.encodeRaw (α := px) bmp
  let ihdr := u32be bmp.size.width ++ u32be bmp.size.height ++
    ByteArray.mk #[Png.PixelFormat.bitDepth (α := px), Png.PixelFormat.colorType (α := px),
      u8 0, u8 0, u8 0]
  let idat := zlibCompressFixedSegmentedParallel raw parallel
  encodeBitmapChunksParallel ihdr ByteArray.empty idat parallel

/-- Checked entry point for segmented fixed-Huffman parallel bitmap encoding. -/
def encodeBitmapFixedSegmentedCheckedParallel {px : Type u}
    [Bitmaps.PixelFormat px] [Png.PixelFormat px]
    (bmp : Bitmap px) (parallel : PngParallelOptions := {}) :
    Except String ByteArray :=
  if hw : bmp.size.width < UInt32.size then
    if hh : bmp.size.height < UInt32.size then
      Except.ok (encodeBitmapFixedSegmentedParallel (px := px) bmp hw hh parallel)
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
