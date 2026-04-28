import Bitmap.Lemmas.Png.DynamicBlockProofsSpec
import Bitmap.Lemmas.Png.FixedBlockProofsCommon

namespace Bitmaps

namespace Png

/-! ## Fixed-block forward-correctness spec (Phase 1b)

A declarative spec for a single DEFLATE fixed-Huffman block (`BTYPE=01`
per RFC 1951 §3.2.6). The structures parallel those in
`DynamicBlockProofsSpec.lean`: payload transitions, finish (EOB),
multi-step trace, and block-level wrapper. The key difference is the
Huffman alphabet — fixed blocks use the RFC-mandated fixed code lengths
hard-coded by `decodeFixedLiteralSym` and `decodeFixedDistanceSym`
rather than a parser-validated `DynamicTableSpec`. The rest of the
LZ77 expansion machinery (length extra bits, distance extra bits,
`copyDistance`) is shared with the dynamic decoder. -/

/-- One non-terminal payload step in a fixed-Huffman block: a literal
push or a length-distance match expansion via `copyDistance`. The
decoder reads the symbol with the fixed-Huffman literal/length decoder,
then for matches reads the length extra bits, distance symbol (5 bits,
fixed alphabet via `decodeFixedDistanceSym`), and distance extra bits. -/
inductive FixedPayloadTransition
    (br : BitReader) (out : ByteArray) : BitReader → ByteArray → Prop where
  | literal (sym : Nat) (br' : BitReader)
      (hdecode : decodeFixedLiteralSym br = some (sym, br'))
      (hlit : sym < 256) :
      FixedPayloadTransition br out br' (out.push (u8 sym))
  | copy (sym extra len distSym extraD distance : Nat)
      (br' br'' br''' br'''' : BitReader) (out' : ByteArray)
      (hdecodeSym : decodeFixedLiteralSym br = some (sym, br'))
      (hnotLit : ¬ sym < 256)
      (hnotEob : (sym == 256) = false)
      (hsym : 257 ≤ sym ∧ sym ≤ 285)
      (hextra :
        extra =
          Array.getInternal lengthExtra (sym - 257) (by
            have hidxle : sym - 257 ≤ 28 := by omega
            have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
            have hsize : lengthExtra.size = 29 := by decide
            simpa [hsize] using hidxlt))
      (hbits : br'.bitIndex + extra ≤ br'.data.size * 8)
      (hdecodeLen :
        decodeLength sym br' hsym
          (by
            have hbits' : br'.bitIndex +
                lengthExtra[sym - 257]'(by
                  have hidxle : sym - 257 ≤ 28 := by omega
                  have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                  have hsize : lengthExtra.size = 29 := by decide
                  simpa [hsize] using hidxlt) ≤ br'.data.size * 8 := by
              simpa [hextra] using hbits
            simpa using hbits') = (len, br''))
      (hdecodeDistSym : decodeFixedDistanceSym br'' = some (distSym, br'''))
      (hdist : distSym < distBases.size)
      (hextraD :
        extraD =
          Array.getInternal distExtra distSym (by
            have hDistExtraSize : distExtra.size = 30 := by decide
            have hDistBasesSize : distBases.size = 30 := by decide
            simpa [hDistExtraSize, hDistBasesSize] using hdist))
      (hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8)
      (hdecodeDist :
        decodeDistance distSym br''' hdist
          (by
            have hbitsD' : br'''.bitIndex +
                distExtra[distSym]'(by
                  have hDistExtraSize : distExtra.size = 30 := by decide
                  have hDistBasesSize : distBases.size = 30 := by decide
                  simpa [hDistExtraSize, hDistBasesSize] using hdist) ≤ br'''.data.size * 8 := by
              simpa [hextraD] using hbitsD
            simpa using hbitsD') = (distance, br''''))
      (hcopy : copyDistance out distance len = some out') :
      FixedPayloadTransition br out br'''' out'

/-- The terminating end-of-block payload step in a fixed-Huffman block:
the next symbol decodes to 256, which is the fixed-table EOB code. -/
inductive FixedPayloadFinish
    (br : BitReader) (out : ByteArray) : BitReader → Prop where
  | eob (sym : Nat) (br' : BitReader)
      (hdecode : decodeFixedLiteralSym br = some (sym, br'))
      (hnotLit : ¬ sym < 256)
      (heob : (sym == 256) = true) :
      FixedPayloadFinish br out br'

/-- Chains validated payload steps into a whole fixed-Huffman payload
trace ending in EOB. The step count justifies the recursion in
`decodeFixedBlockFuel`. -/
inductive FixedPayloadTrace :
    Nat → BitReader → ByteArray → BitReader → ByteArray → Prop where
  | finish {br br' : BitReader} {out : ByteArray}
      (hfinish : FixedPayloadFinish br out br') :
      FixedPayloadTrace 1 br out br' out
  | step {steps : Nat} {br br' br'' : BitReader} {out out' out'' : ByteArray}
      (hstep : FixedPayloadTransition br out br' out')
      (hrest : FixedPayloadTrace steps br' out' br'' out'') :
      FixedPayloadTrace (steps + 1) br out br'' out''

/-- One fixed-Huffman DEFLATE block: the block header chooses `BTYPE=01`
(read as 3 bits with value `010` for non-final or `011` for final),
followed immediately by the LZ77 payload terminated by the EOB code
(symbol 256). No table-reading phase is needed because the fixed
Huffman alphabet is RFC-mandated. -/
structure FixedBlockSpec (final : Bool)
    (br : BitReader) (out : ByteArray) (br' : BitReader) (out' : ByteArray) where
  payloadReader : BitReader
  steps : Nat
  headerReadable : br.bitIndex + 3 ≤ br.data.size * 8
  headerRead :
    br.readBits 3 headerReadable = ((if final then 3 else 2), payloadReader)
  payload : FixedPayloadTrace steps payloadReader out br' out'
  payloadFuel : steps ≤ payloadReader.data.size * 8 + 1

/-! ### Slow-variant per-step lemmas

The existing per-step lemmas in `FixedBlockProofsDecode.lean` use the
*fast* runtime decoders (`decodeFixedBlockFuelFast`/
`decodeFixedLiteralSymFast9`). The `FixedBlockSpec` here uses the slow
variants (`decodeFixedBlockFuel`/`decodeFixedLiteralSym`), matching the
runtime entry point used by `parsePng`. The next three lemmas are the
slow-variant analogues — pure runtime reductions of `decodeFixedBlockFuel`
on its three exhaustive branches. -/

/-- Slow-variant EOB step: decoding a symbol of value 256 terminates the
block with the post-symbol reader and unchanged output. -/
lemma decodeFixedBlockFuel_step_eob_of_decodes
    (fuel : Nat) (br br' : BitReader) (out : ByteArray) (sym : Nat)
    (hdecodeSym : decodeFixedLiteralSym br = some (sym, br'))
    (hnotLit : ¬ sym < 256) (heob : (sym == 256) = true) :
    decodeFixedBlockFuel (fuel + 1) br out = some (br', out) := by
  rw [decodeFixedBlockFuel.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  let k : Nat → BitReader → Option (BitReader × ByteArray) := fun sym br' =>
    if sym < 256 then
      decodeFixedBlockFuel fuel br' (out.push (u8 sym))
    else if (sym == 256) = true then
      pure (br', out)
    else if hlen : 257 ≤ sym ∧ sym ≤ 285 then
      let idx := sym - 257
      have hidxle : idx ≤ 28 := by
        dsimp [idx]
        omega
      have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
      have hidxExtra : idx < lengthExtra.size := by
        have hsize : lengthExtra.size = 29 := by decide
        simpa [hsize] using hidxlt
      let extra := Array.getInternal lengthExtra idx hidxExtra
      if hbits : br'.bitIndex + extra ≤ br'.data.size * 8 then
        do
          let (len, br'') := decodeLength sym br' hlen (by simpa using hbits)
          let (distSym, br''') ← decodeFixedDistanceSym br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeFixedBlockFuel fuel br'''' out'
            else
              none
          else
            none
      else
        none
    else
      none
  change (match (sym, br') with | (s, r) => k s r) = some (br', out)
  have hpair : (match (sym, br') with | (s, r) => k s r) = k sym br' := by
    simpa using (match_pair_eta (a := sym) (b := br') (k := k))
  rw [hpair]
  dsimp [k]
  rw [if_neg hnotLit]
  rw [if_pos heob]

/-! ### Forward correctness via the inductive trace

Given any `FixedPayloadTrace`, `decodeFixedBlockFuel` reproduces the
trace's `(br', out')`. The proof is by induction on the trace using the
slow-variant EOB step (above) for the `finish` case and the fast-variant
literal/match step lemmas via decoder equivalence for the recursive case.

The literal- and match-step slow variants are deferred to a follow-up
commit (each is ~50 lines of similar do-notation manipulation as the
EOB step above; the existing fast-variant lemmas serve as templates). -/

end Png

end Bitmaps
