import Bitmap.Lemmas.Png.EncodeDecodeBase

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Stored-block forward-correctness spec

A declarative spec for a single DEFLATE stored block (`BTYPE=00` per
RFC 1951 §3.2.4) and the multi-block stream that the runtime
`inflateStored` accepts. The spec is byte-aligned because stored blocks
themselves are byte-aligned: the runtime reads the BFINAL/BTYPE header
from byte 0 of the block, the LEN/NLEN pair from bytes 1-4, and the
payload from bytes 5..5+LEN.

Phase 1a of the external-PNG plan; consumed by Phase 2's mixed
`BlockSpec` ADT and Phase 5's end-to-end composition. -/

/-- A single stored DEFLATE block: the BFINAL bit, the payload, and the
RFC-1951 size constraint (LEN field is 16-bit unsigned). Parameters
deliberately mirror `DynamicBlockSpec` from `DynamicBlockProofsSpec.lean`. -/
structure StoredBlockSpec where
  final : Bool
  payload : ByteArray
  hsize : payload.size ≤ 0xFFFF

/-- Concrete bytes for this block followed by an arbitrary continuation. The
runtime decoder reads `5 + payload.size` bytes from the front, validates the
header/LEN/NLEN, then either returns the payload (if `final`) or recurses
into `rest`. -/
def StoredBlockSpec.bytesWithRest (s : StoredBlockSpec) (rest : ByteArray) : ByteArray :=
  storedBlock s.payload s.final ++ rest

/-- Standalone bytes of a single stored block (no continuation). -/
def StoredBlockSpec.bytes (s : StoredBlockSpec) : ByteArray :=
  s.bytesWithRest ByteArray.empty

/-- Forward correctness for a single stored block: `inflateStoredAux` on the
spec's bytes-with-rest exactly reproduces the runtime's recursive shape —
return the payload and `rest` immediately when `BFINAL=1`, otherwise
descend into `rest` and prepend the payload to whatever the recursion
yields. This is a thin wrapper over `inflateStoredAux_storedBlock` from
`EncodeDecodeBase.lean`. -/
theorem storedBlockSpec_decode_correct (s : StoredBlockSpec) (rest : ByteArray)
    (hpos : 0 < (s.bytesWithRest rest).size) :
    inflateStoredAux (s.bytesWithRest rest) hpos =
      if s.final then some (s.payload, rest)
      else
        if hrest : 0 < rest.size then
          match inflateStoredAux rest hrest with
          | some (tail, rest') => some (s.payload ++ tail, rest')
          | none => none
        else
          none := by
  unfold StoredBlockSpec.bytesWithRest
  exact inflateStoredAux_storedBlock s.payload rest s.final s.hsize hpos

/-- A complete stored DEFLATE stream: a non-empty sequence of stored blocks
where only the last carries `BFINAL=1`, matching the runtime's recursive
shape in `inflateStoredAux`. The relation pairs the byte stream with the
concatenated payload it decodes to. -/
inductive StoredDeflateStreamSpec : ByteArray → ByteArray → Prop where
  | final (block : StoredBlockSpec) (hfinal : block.final = true) :
      StoredDeflateStreamSpec block.bytes block.payload
  | more (block : StoredBlockSpec) (hfinal : block.final = false)
      (restBytes restOut : ByteArray)
      (hRest : StoredDeflateStreamSpec restBytes restOut) :
      StoredDeflateStreamSpec (block.bytesWithRest restBytes) (block.payload ++ restOut)

/-- The byte stream of any `StoredDeflateStreamSpec` is non-empty: the first
block contributes at least the 5-byte header, regardless of payload size. -/
lemma StoredDeflateStreamSpec.bytes_pos {bytes out : ByteArray}
    (h : StoredDeflateStreamSpec bytes out) : 0 < bytes.size := by
  induction h with
  | final block _ =>
      unfold StoredBlockSpec.bytes StoredBlockSpec.bytesWithRest
      simp [storedBlock_size]
  | more block _ restBytes restOut _ _ =>
      unfold StoredBlockSpec.bytesWithRest
      simp [storedBlock_size, ByteArray.size_append]
      omega

/-- Forward correctness for stored DEFLATE streams: any byte stream matching
the inductive `StoredDeflateStreamSpec` shape is decoded by `inflateStoredAux`
into the spec's payload, with no remaining bytes. The proof is by induction
on the spec; the base case applies `storedBlockSpec_decode_correct`, and
the inductive case combines that one-block result with the IH. -/
theorem storedDeflateStreamSpec_decode_correct
    {bytes out : ByteArray} (h : StoredDeflateStreamSpec bytes out) :
    inflateStoredAux bytes (StoredDeflateStreamSpec.bytes_pos h) = some (out, ByteArray.empty) := by
  induction h with
  | final block hfinal =>
      have hpos : 0 < block.bytes.size :=
        StoredDeflateStreamSpec.bytes_pos (StoredDeflateStreamSpec.final block hfinal)
      have hbase := storedBlockSpec_decode_correct block ByteArray.empty hpos
      simp [hfinal] at hbase
      simpa [StoredBlockSpec.bytes] using hbase
  | more block hfinal restBytes restOut hRest ih =>
      have hpos : 0 < (block.bytesWithRest restBytes).size :=
        StoredDeflateStreamSpec.bytes_pos
          (StoredDeflateStreamSpec.more block hfinal restBytes restOut hRest)
      have hbase := storedBlockSpec_decode_correct block restBytes hpos
      have hrestPos : 0 < restBytes.size := StoredDeflateStreamSpec.bytes_pos hRest
      simp [hfinal, hrestPos, ih] at hbase
      exact hbase

end Lemmas

end Bitmaps
