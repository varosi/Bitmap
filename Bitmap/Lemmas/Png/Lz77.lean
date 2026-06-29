import Bitmap.Lemmas.Png.FixedBlockProofsCommon

namespace Bitmaps

namespace Png

/-- Public LZ77 length metadata is the fixed-Huffman match-length metadata,
packaged under the encoder-facing name used by full LZ77 payload writers. -/
lemma deflateLengthInfo_spec_internal (len : Nat) (hlo : 3 ≤ len) (hhi : len ≤ 258) :
    match deflateLengthInfo len with
    | (sym, extraBits, extraLen) =>
        ∃ _hsym : 257 ≤ sym ∧ sym ≤ 285,
          ∃ hidxBase : sym - 257 < lengthBases.size,
            ∃ hidxExtra : sym - 257 < lengthExtra.size,
              extraLen = Array.getInternal lengthExtra (sym - 257) hidxExtra ∧
              Array.getInternal lengthBases (sym - 257) hidxBase + extraBits = len ∧
              extraBits < 2 ^ extraLen := by
  simpa [deflateLengthInfo] using fixedLenMatchInfo_spec_internal len hlo hhi

/-- Successful distance-table search returns metadata that agrees with the
DEFLATE distance decoder tables. This isolates the recursive search proof. -/
lemma deflateDistanceInfoSearch_some_spec_get!
    {distance start sym extraBits extraLen : Nat}
    (hinfo :
      deflateDistanceInfoSearch distance start = some (sym, extraBits, extraLen)) :
    sym < distBases.size ∧
      extraLen = distExtra[sym]! ∧
      distBases[sym]! + extraBits = distance ∧
      extraBits < 2 ^ extraLen := by
  classical
  have hk :
      ∀ k, ∀ pos,
        deflateDistanceBases.size - pos = k →
        deflateDistanceInfoSearch distance pos = some (sym, extraBits, extraLen) →
          sym < distBases.size ∧
            extraLen = distExtra[sym]! ∧
            distBases[sym]! + extraBits = distance ∧
            extraBits < 2 ^ extraLen := by
    intro k
    induction k with
    | zero =>
        intro pos hk hinfo
        have hnot : ¬ pos < deflateDistanceBases.size := by omega
        rw [deflateDistanceInfoSearch.eq_1] at hinfo
        simp [hnot] at hinfo
    | succ k ih =>
        intro pos hk hinfo
        rw [deflateDistanceInfoSearch.eq_1] at hinfo
        by_cases hpos : pos < deflateDistanceBases.size
        · simp [hpos] at hinfo
          let base := deflateDistanceBases[pos]
          let extraLen0 := deflateDistanceExtraLens[pos]!
          let limit := base + (1 <<< extraLen0)
          by_cases hmatch : base ≤ distance ∧ distance < limit
          · rw [if_pos (by simpa [base, extraLen0, limit] using hmatch)] at hinfo
            have hdist : pos < distBases.size := by
              simpa [distBases, deflateDistanceBases] using hpos
            have hbaseEq : distBases[pos]! = base := by
              rw [getElem!_pos distBases pos hdist]
              simp [base, distBases, deflateDistanceBases]
            have hbaseLe : base ≤ distance := by
              exact hmatch.1
            have hdistLt : distance < base + 2 ^ extraLen0 := by
              simpa [base, extraLen0, limit, Nat.shiftLeft_eq, Nat.one_mul] using hmatch.2
            cases hinfo
            refine ⟨hdist, ?_, ?_, ?_⟩
            · simp [distExtra, deflateDistanceExtraLens]
            · rw [hbaseEq]
              omega
            · dsimp [base, extraLen0] at hbaseLe hdistLt
              omega
          · rw [if_neg (by simpa [base, extraLen0, limit] using hmatch)] at hinfo
            have hk' : deflateDistanceBases.size - (pos + 1) = k := by omega
            exact ih (pos + 1) hk' hinfo
        · simp [hpos] at hinfo
  exact hk (deflateDistanceBases.size - start) start rfl hinfo

/-- If `deflateDistanceInfo?` returns metadata, the encoded distance symbol and
extra bits reconstruct the original distance in the decoder tables. -/
lemma deflateDistanceInfo?_some_spec_get!
    {distance sym extraBits extraLen : Nat}
    (hinfo : deflateDistanceInfo? distance = some (sym, extraBits, extraLen)) :
    sym < distBases.size ∧
      extraLen = distExtra[sym]! ∧
      distBases[sym]! + extraBits = distance ∧
      extraBits < 2 ^ extraLen := by
  unfold deflateDistanceInfo? at hinfo
  by_cases hvalid : 1 ≤ distance && distance ≤ deflateMaxDistance
  · exact deflateDistanceInfoSearch_some_spec_get!
      (distance := distance) (start := 0) (sym := sym)
      (extraBits := extraBits) (extraLen := extraLen)
      (by simpa [hvalid] using hinfo)
  · simp [hvalid] at hinfo

end Png

end Bitmaps
