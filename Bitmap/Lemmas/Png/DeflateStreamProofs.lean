import Bitmap.Lemmas.Png.DeflateStreamSpec
import Bitmap.Lemmas.Png.DynamicBlockProofsLoop
import Bitmap.Lemmas.Png.FixedBlockFastSlowBridge

set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false

namespace Bitmaps

namespace Png

open Bitmaps.Lemmas

/-! ## Mixed DEFLATE stream forward correctness (Phase 2)

This file proves `deflateStreamSpec_decode_correct`: any well-formed
`DeflateStreamSpec` is accepted by the runtime `zlibDecompressLoop`.
The proof composes three per-block-type step lemmas (stored / fixed /
dynamic) with an induction over the stream constructor. The fixed
branch uses `fixedBlockSpec_decode_correct_fast` from Option A, and the
dynamic branch reuses the existing
`zlibDecompressLoopFuel_step_dynamic_{final,nonfinal}_of_trace`
lemmas. The stored branch is new to this file. -/

/-! ### Stored block — runtime path

`zlibDecompressLoopFuel` reads the 3-bit header (value `bfinal` since
`BTYPE=00`), aligns to a byte boundary, parses `LEN`/`NLEN`, validates
the RFC-1951 invariant, copies `LEN` bytes from the data into `out`,
and advances the reader to the position right after the payload. -/

set_option maxHeartbeats 6000000 in
lemma zlibDecompressLoopFuel_step_stored_final_of_spec
    (fuel : Nat) {br brNext : BitReader} {out outNext : ByteArray}
    (block : StoredBlockBitSpec true br out brNext outNext) :
    zlibDecompressLoopFuel (fuel + 1) br out = some (brNext, outNext) := by
  rcases block with
    ⟨payload, brHeader, brAligned, hsize, hcond, hread3, hAligned, hLayout,
      hLEN, hNLEN, hPayload, hOut, hNext⟩
  -- Layout / arithmetic facts.
  have hbytePos_lt : brAligned.bytePos + 3 < brAligned.data.size := by
    have h0 : 0 ≤ payload.size := payload.size.zero_le; omega
  have hsum : payload.size + (0xFFFF - payload.size) = 0xFFFF := by
    have : payload.size ≤ 0xFFFF := hsize; omega
  have hstart_le : ¬ (brAligned.bytePos + 4 + payload.size > brAligned.data.size) := by
    intro h; omega
  rcases hNext with ⟨hData, hBytePos, hBitPos⟩
  have hRdrEq : (BitReader.mk brAligned.data (brAligned.bytePos + 4 + payload.size) 0
        (Nat.le_of_not_gt hstart_le) (by intro _; rfl) (by decide)) = brNext := by
    have ⟨bd, bb, bp, h1, h2, h3⟩ := brNext
    simp at hData hBytePos hBitPos
    subst hData hBytePos hBitPos
    rfl
  rw [zlibDecompressLoopFuel]
  simp [hcond, hread3, ← hAligned, hbytePos_lt, hLEN, hNLEN, hsum, hstart_le,
        hPayload, hRdrEq, hOut]

set_option maxHeartbeats 6000000 in
lemma zlibDecompressLoopFuel_step_stored_nonfinal_of_spec
    (fuel : Nat) {br brMid brFinal : BitReader} {out outMid outFinal : ByteArray}
    (block : StoredBlockBitSpec false br out brMid outMid)
    (hrest : zlibDecompressLoopFuel fuel brMid outMid = some (brFinal, outFinal)) :
    zlibDecompressLoopFuel (fuel + 1) br out = some (brFinal, outFinal) := by
  rcases block with
    ⟨payload, brHeader, brAligned, hsize, hcond, hread3, hAligned, hLayout,
      hLEN, hNLEN, hPayload, hOut, hNext⟩
  have hbytePos_lt : brAligned.bytePos + 3 < brAligned.data.size := by
    have h0 : 0 ≤ payload.size := payload.size.zero_le; omega
  have hsum : payload.size + (0xFFFF - payload.size) = 0xFFFF := by
    have : payload.size ≤ 0xFFFF := hsize; omega
  have hstart_le : ¬ (brAligned.bytePos + 4 + payload.size > brAligned.data.size) := by
    intro h; omega
  rcases hNext with ⟨hData, hBytePos, hBitPos⟩
  have hRdrEq : (BitReader.mk brAligned.data (brAligned.bytePos + 4 + payload.size) 0
        (Nat.le_of_not_gt hstart_le) (by intro _; rfl) (by decide)) = brMid := by
    have ⟨bd, bb, bp, h1, h2, h3⟩ := brMid
    simp at hData hBytePos hBitPos
    subst hData hBytePos hBitPos
    rfl
  rw [zlibDecompressLoopFuel]
  simp [hcond, hread3, ← hAligned, hbytePos_lt, hLEN, hNLEN, hsum, hstart_le,
        hPayload, hRdrEq, ← hOut, hrest]

/-! ### Fixed block — runtime path

`zlibDecompressLoopFuel` reads the 3-bit header (`2` for non-final,
`3` for final), then calls `decodeFixedBlock` which is
`decodeFixedBlockFuelFast (data.size * 8 + 1)`. Our Option A bridge
gives this via `fixedBlockSpec_decode_correct_fast`. -/

set_option maxHeartbeats 6000000 in
lemma zlibDecompressLoopFuel_step_fixed_final_of_spec
    (fuel : Nat) {br brNext : BitReader} {out outNext : ByteArray}
    (block : FixedBlockSpec true br out brNext outNext) :
    zlibDecompressLoopFuel (fuel + 1) br out = some (brNext, outNext) := by
  have hcond := block.headerReadable
  have hread3 := block.headerRead
  -- The fast decoder accepts the spec at runtime fuel.
  have hslow :
      decodeFixedBlockFuel (block.payloadReader.data.size * 8 + 1)
        block.payloadReader out = some (brNext, outNext) :=
    decodeFixedBlockFuel_of_trace block.payload block.payloadFuel
  have hfast :
      decodeFixedBlock block.payloadReader out = some (brNext, outNext) := by
    unfold decodeFixedBlock decodeFixedBlockFast
    rw [decodeFixedBlockFuelFast_eq_decodeFixedBlockFuel]
    exact hslow
  rw [zlibDecompressLoopFuel]
  simp [hcond, hread3, hfast]

set_option maxHeartbeats 6000000 in
lemma zlibDecompressLoopFuel_step_fixed_nonfinal_of_spec
    (fuel : Nat) {br brMid brFinal : BitReader} {out outMid outFinal : ByteArray}
    (block : FixedBlockSpec false br out brMid outMid)
    (hrest : zlibDecompressLoopFuel fuel brMid outMid = some (brFinal, outFinal)) :
    zlibDecompressLoopFuel (fuel + 1) br out = some (brFinal, outFinal) := by
  have hcond := block.headerReadable
  have hread3 := block.headerRead
  have hslow :
      decodeFixedBlockFuel (block.payloadReader.data.size * 8 + 1)
        block.payloadReader out = some (brMid, outMid) :=
    decodeFixedBlockFuel_of_trace block.payload block.payloadFuel
  have hfast :
      decodeFixedBlock block.payloadReader out = some (brMid, outMid) := by
    unfold decodeFixedBlock decodeFixedBlockFast
    rw [decodeFixedBlockFuelFast_eq_decodeFixedBlockFuel]
    exact hslow
  rw [zlibDecompressLoopFuel]
  simp [hcond, hread3, hfast, hrest]

/-! ### BlockSpec-level step lemma

Dispatches on the `BlockSpec` constructor and calls the appropriate
per-block-type step lemma. -/

set_option maxHeartbeats 6000000 in
lemma zlibDecompressLoopFuel_step_block_final_of_spec
    (fuel : Nat) {br brNext : BitReader} {out outNext : ByteArray}
    (block : BlockSpec true br out brNext outNext) :
    zlibDecompressLoopFuel (fuel + 1) br out = some (brNext, outNext) := by
  cases block with
  | stored sb =>
      exact zlibDecompressLoopFuel_step_stored_final_of_spec fuel sb
  | fixed fb =>
      exact zlibDecompressLoopFuel_step_fixed_final_of_spec fuel fb
  | dynamic db =>
      rcases db with ⟨spec, brHeader, brPayload, steps, hcond, hread3, hspec, htrace, hsteps⟩
      exact zlibDecompressLoopFuel_step_dynamic_final_of_trace
        (fuel := fuel) (br := br) (brHeader := brHeader)
        (brPayload := brPayload) (brFinal := brNext)
        (out := out) (out' := outNext) (spec := spec)
        hcond (by simpa using hread3) hspec htrace hsteps

set_option maxHeartbeats 6000000 in
lemma zlibDecompressLoopFuel_step_block_nonfinal_of_spec
    (fuel : Nat) {br brMid brFinal : BitReader} {out outMid outFinal : ByteArray}
    (block : BlockSpec false br out brMid outMid)
    (hrest : zlibDecompressLoopFuel fuel brMid outMid = some (brFinal, outFinal)) :
    zlibDecompressLoopFuel (fuel + 1) br out = some (brFinal, outFinal) := by
  cases block with
  | stored sb =>
      exact zlibDecompressLoopFuel_step_stored_nonfinal_of_spec fuel sb hrest
  | fixed fb =>
      exact zlibDecompressLoopFuel_step_fixed_nonfinal_of_spec fuel fb hrest
  | dynamic db =>
      rcases db with ⟨spec, brHeader, brPayload, steps, hcond, hread3, hspec, htrace, hsteps⟩
      exact zlibDecompressLoopFuel_step_dynamic_nonfinal_of_trace
        (fuel := fuel) (br := br) (brHeader := brHeader)
        (brPayload := brPayload) (brNext := brMid) (brFinal := brFinal)
        (out := out) (outNext := outMid) (outFinal := outFinal)
        (spec := spec)
        hcond (by simpa using hread3) hspec htrace hsteps hrest

/-! ### Main forward-correctness theorem -/

/-- Phase 2 final: any validated `DeflateStreamSpec` is accepted by the
runtime fuel-bounded `zlibDecompressLoopFuel`. The fuel argument must
cover the block count. -/
lemma deflateStreamSpec_decodeFuel_correct
    {blocks fuel : Nat} {br br' : BitReader} {out out' : ByteArray}
    (hstream : DeflateStreamSpec blocks br out br' out')
    (hfuel : blocks ≤ fuel) :
    zlibDecompressLoopFuel fuel br out = some (br', out') := by
  induction hstream generalizing fuel with
  | final block =>
      cases fuel with
      | zero => cases hfuel
      | succ fuel =>
          exact zlibDecompressLoopFuel_step_block_final_of_spec fuel block
  | more block _rest ih =>
      rename_i blocks0 br0 brMid brFinal out0 outMid outFinal
      cases fuel with
      | zero => cases hfuel
      | succ fuel =>
          have hrest : zlibDecompressLoopFuel fuel brMid outMid = some (brFinal, outFinal) := by
            exact ih (by omega)
          exact zlibDecompressLoopFuel_step_block_nonfinal_of_spec fuel block hrest

/-- Public DEFLATE stream forward-correctness theorem against the
unparametrised `zlibDecompressLoop`. -/
lemma deflateStreamSpec_decode_correct
    {blocks : Nat} {br br' : BitReader} {out out' : ByteArray}
    (hstream : DeflateStreamSpec blocks br out br' out')
    (hfuel : blocks ≤ br.data.size * 8 + 1) :
    zlibDecompressLoop br out = some (br', out') := by
  change zlibDecompressLoopFuel (br.data.size * 8 + 1) br out = some (br', out')
  exact deflateStreamSpec_decodeFuel_correct hstream hfuel

end Png

end Bitmaps
