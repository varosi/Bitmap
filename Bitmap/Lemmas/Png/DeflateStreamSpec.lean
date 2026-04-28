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

The forward-correctness theorem for this spec faces two open issues
that are kept here as documentation of the remaining work:

1. **Stored block, bit alignment**: the runtime stored-block path in
   `zlibDecompressLoopFuel` reads the 3-bit header, byte-aligns the
   reader, then reads LEN/NLEN/payload from the byte stream. The
   existing byte-aligned `Bitmaps.Lemmas.StoredBlockSpec` from
   `StoredBlockProofsSpec.lean` does not yet have a BitReader-based
   wrapper that handles the alignment.

2. **Fixed block, fast vs. slow**: the runtime's fixed branch calls
   `decodeFixedBlockFast = decodeFixedBlockFuelFast`, but Phase 1b's
   `fixedBlockSpec_decode_correct` proves correctness against the
   *slow* `decodeFixedBlockFuel`. Bridging requires either an
   extensional equivalence
   `decodeFixedBlockFuelFast = decodeFixedBlockFuel`, or a parallel
   `FixedBlockSpec_fast_decode_correct` proved against the existing
   fast step lemmas in `FixedBlockProofsDecode.lean`.

Both bridges are well-defined isolated commits; the scaffold below
exposes the shape they will plug into. -/

/-- One DEFLATE block — a 3-way sum over the supported block types.
The stored case wraps a byte-level `Lemmas.StoredBlockSpec` plus the
bit-aligned 3-bit header and post-block byte-aligned reader; the
fixed and dynamic cases reuse the existing block specs which already
include their headers. -/
inductive BlockSpec : Bool → BitReader → ByteArray → BitReader → ByteArray → Type where
  | fixed {final : Bool} {br br' : BitReader} {out out' : ByteArray}
      (block : FixedBlockSpec final br out br' out') :
      BlockSpec final br out br' out'
  | dynamic {final : Bool} {br br' : BitReader} {out out' : ByteArray}
      (block : DynamicBlockSpec final br out br' out') :
      BlockSpec final br out br' out'
  -- The `stored` variant is deferred to a follow-up commit; it requires a
  -- BitReader-based wrapper around `Bitmaps.Lemmas.StoredBlockSpec` that
  -- threads through the runtime's `BitReader.alignByte` step.

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
