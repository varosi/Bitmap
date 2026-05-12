import Bitmap.Lemmas.Png.FixedBlockProofsSpec
import Bitmap.Lemmas.Png.StoredBlockProofsSpec

namespace Bitmaps

namespace Png

/-! ## Mixed DEFLATE stream spec (Phase 2 scaffold)

A 3-way sum type for one DEFLATE block (stored / fixed / dynamic) and an
inductive `DeflateStreamSpec` chaining blocks until the `BFINAL=1`
terminator. Mirrors `DynamicDeflateStreamSpec` but generalises to any
block type, matching the runtime `zlibDecompressLoopFuel`'s 3-way
dispatch on `BTYPE`.

### Bridging / runtime mismatch

The forward-correctness theorem for this spec is now unblocked: the
runtime's fixed branch calls `decodeFixedBlockFast = decodeFixedBlockFuelFast`,
and `FixedBlockFastSlowBridge.lean` proves the extensional equivalence
`decodeFixedBlockFuelFast = decodeFixedBlockFuel` (per-symbol bridge
`decodeFixedLiteralSymFast9_eq_decodeFixedLiteralSym` + fuel-level lifting
`decodeFixedBlockFuelFast_eq_decodeFixedBlockFuel`). The fast-variant
corollary `fixedBlockSpec_decode_correct_fast` composes with the slow
`fixedBlockSpec_decode_correct` from Phase 1b. -/

/-! ### Stored-block BitReader wrapper

The byte-aligned `Bitmaps.Lemmas.StoredBlockSpec` cannot directly
participate in a BitReader-based stream because the runtime's
stored-block path goes through `BitReader.alignByte` after reading the
3-bit BFINAL/BTYPE header. The structure below adds that bit-level
framing, capturing the data the runtime needs at each step. -/

/-- A stored DEFLATE block expressed against a `BitReader` — the framing
the runtime sees inside `zlibDecompressLoopFuel`'s stored branch:

  * 3-bit header (BFINAL + `BTYPE=00`) is read at the current bit
    position, packed as `if final then 1 else 0`.
  * After the header, the runtime calls `BitReader.alignByte` to skip
    any partial-byte padding before the LEN/NLEN/payload bytes.
  * `LEN` (2 bytes, little-endian), `NLEN` (2 bytes, little-endian)
    and the payload follow, with the RFC-1951 invariant
    `LEN + NLEN = 0xFFFF`.
  * The final reader is byte-aligned at the position right after the
    payload bytes. -/
structure StoredBlockBitSpec (final : Bool)
    (br : BitReader) (out : ByteArray)
    (brNext : BitReader) (outNext : ByteArray) where
  /-- The payload bytes carried by this stored block. -/
  payload : ByteArray
  /-- The post-header reader (after the 3 BFINAL/BTYPE bits, before alignment). -/
  brHeader : BitReader
  /-- The byte-aligned reader (after `BitReader.alignByte`). -/
  brAligned : BitReader
  /-- LEN payload-size bound: 16-bit unsigned, max `0xFFFF`. -/
  hsize : payload.size ≤ 0xFFFF
  /-- 3 bits readable for the header. -/
  headerReadable : br.bitIndex + 3 ≤ br.data.size * 8
  /-- The 3-bit header reads as `BFINAL + 2 * BTYPE = if final then 1 else 0`
      (BTYPE=00 because this is a stored block). -/
  headerRead : br.readBits 3 headerReadable = ((if final then 1 else 0), brHeader)
  /-- The aligned reader is the byte-aligned form of the post-header reader. -/
  hAligned : brAligned = brHeader.alignByte
  /-- Enough bytes for LEN + NLEN + payload. -/
  hLayout : brAligned.bytePos + 4 + payload.size ≤ brAligned.data.size
  /-- The 2-byte LEN field reads as the payload size. -/
  hLEN :
    readU16LE brAligned.data brAligned.bytePos
        (by have := hLayout; have := payload.size.zero_le; omega) = payload.size
  /-- The 2-byte NLEN field is `0xFFFF - LEN` (RFC-1951 invariant). -/
  hNLEN :
    readU16LE brAligned.data (brAligned.bytePos + 2)
        (by have := hLayout; have := payload.size.zero_le; omega) = 0xFFFF - payload.size
  /-- The payload bytes match what the runtime will extract. -/
  hPayload :
    brAligned.data.extract (brAligned.bytePos + 4)
        (brAligned.bytePos + 4 + payload.size) = payload
  /-- The output is the input concatenated with the payload. -/
  hOut : outNext = out ++ payload
  /-- The final reader is byte-aligned at the position right after the payload. -/
  hNext :
    brNext.data = brAligned.data ∧
    brNext.bytePos = brAligned.bytePos + 4 + payload.size ∧
    brNext.bitPos = 0

/-- One DEFLATE block — a 3-way sum over the supported block types.
The stored case wraps `StoredBlockBitSpec` (the BitReader-framed view
above); the fixed and dynamic cases reuse the existing block specs
which already include their headers. -/
inductive BlockSpec : Bool → BitReader → ByteArray → BitReader → ByteArray → Type where
  | stored {final : Bool} {br br' : BitReader} {out out' : ByteArray}
      (block : StoredBlockBitSpec final br out br' out') :
      BlockSpec final br out br' out'
  | fixed {final : Bool} {br br' : BitReader} {out out' : ByteArray}
      (block : FixedBlockSpec final br out br' out') :
      BlockSpec final br out br' out'
  | dynamic {final : Bool} {br br' : BitReader} {out out' : ByteArray}
      (block : DynamicBlockSpec final br out br' out') :
      BlockSpec final br out br' out'

/-- A complete DEFLATE stream: zero or more non-final blocks followed by
exactly one `BFINAL=1` block. Threads the BitReader and accumulated
output through each block. Mirrors `DynamicDeflateStreamSpec` but
generalises the per-block payload to any `BlockSpec`. -/
inductive DeflateStreamSpec :
    Nat → BitReader → ByteArray → BitReader → ByteArray → Type where
  | final {br br' : BitReader} {out out' : ByteArray}
      (block : BlockSpec true br out br' out') :
      DeflateStreamSpec 1 br out br' out'
  | more {blocks : Nat} {br brMid br' : BitReader} {out outMid out' : ByteArray}
      (block : BlockSpec false br out brMid outMid)
      (rest : DeflateStreamSpec blocks brMid outMid br' out') :
      DeflateStreamSpec (blocks + 1) br out br' out'

/-! ### Forward correctness (deferred)

The public theorem
  `deflateStreamSpec_decode_correct :
     DeflateStreamSpec blocks br out br' out' → blocks ≤ … →
     zlibDecompressLoop br out = some (br', out')`
is deferred to a follow-up commit. Once landed, Phase 5 (end-to-end
`decodeBitmap_external_correct`) becomes a routing exercise composing
this theorem with the container spec, the row-filter spec, and the
zlib envelope.

The proof structure mirrors `dynamicDeflateStreamSpec_decode_correct`
in `DynamicBlockProofsLoop.lean`, but with a 2-way (eventually 3-way)
case split over the `BlockSpec` constructor at each block. The
existing `zlibDecompressLoopFuel_step_dynamic_{final,nonfinal}_of_trace`
lemmas serve as templates; analogous fixed (and stored) step lemmas
need to be added once the bridging issues above are resolved. -/

end Png

end Bitmaps
