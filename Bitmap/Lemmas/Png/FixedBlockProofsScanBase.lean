import Bitmap.Lemmas.Png.FixedBlockProofsCommon

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

def sameByteRunEnd (data : Array UInt8) (b : UInt8) (j : Nat) : Nat :=
  if h : j < data.size then
    if data[j]'h = b then
      sameByteRunEnd data b (j + 1)
    else
      j
  else
    j
termination_by data.size - j
decreasing_by
  have hlt : j < data.size := h
  exact Nat.sub_lt_sub_left (k := j) (m := data.size) (n := j + 1) hlt (Nat.lt_succ_self j)

lemma sameByteRunEnd_ge (data : Array UInt8) (b : UInt8) (j : Nat) :
    j ≤ sameByteRunEnd data b j := by
  rw [sameByteRunEnd.eq_def]
  by_cases h : j < data.size
  · by_cases heq : data[j]'h = b
    · have hrec := sameByteRunEnd_ge data b (j + 1)
      simp [h, heq]
      omega
    · simp [h, heq]
  · simp [h]

lemma sameByteRunEnd_le_size (data : Array UInt8) (b : UInt8) (j : Nat)
    (hj : j ≤ data.size) :
    sameByteRunEnd data b j ≤ data.size := by
  rw [sameByteRunEnd.eq_def]
  by_cases h : j < data.size
  · by_cases heq : data[j]'h = b
    · simp [h, heq]
      exact sameByteRunEnd_le_size data b (j + 1) (Nat.succ_le_of_lt h)
    · simp [h, heq]
      omega
  · simp [h]
    exact hj

lemma sameByteRunEnd_gt_prev
    (data : Array UInt8) (i : Nat) (h : i < data.size) :
    i < sameByteRunEnd data data[i] (i + 1) := by
  have hge : i + 1 ≤ sameByteRunEnd data data[i] (i + 1) :=
    sameByteRunEnd_ge data data[i] (i + 1)
  omega

lemma sameByteRunEnd_stop_ne (data : Array UInt8) (b : UInt8) (j : Nat)
    (hend : sameByteRunEnd data b j < data.size) :
    data[sameByteRunEnd data b j]'hend ≠ b := by
  rw [sameByteRunEnd.eq_def] at hend
  by_cases h : j < data.size
  · by_cases heq : data[j]'h = b
    · simp [h, heq] at hend
      have hs : sameByteRunEnd data b j = sameByteRunEnd data b (j + 1) := by
        rw [sameByteRunEnd.eq_def]
        simp [h, heq]
      simpa [hs] using (sameByteRunEnd_stop_ne data b (j + 1) hend)
    · have hs : sameByteRunEnd data b j = j := by
        rw [sameByteRunEnd.eq_def]
        simp [h, heq]
      simpa [hs] using heq
  · simp [sameByteRunEnd.eq_def, h] at hend

lemma byteArrayFromArray_sameByteRunEnd_pushRepeat
    (data : Array UInt8) (b : UInt8) (i : Nat) (out : ByteArray) :
    byteArrayFromArray data i out =
      byteArrayFromArray data (sameByteRunEnd data b i)
        (pushRepeat out b (sameByteRunEnd data b i - i)) := by
  classical
  by_cases h : i < data.size
  · by_cases heq : data[i]'h = b
    · have hrec :=
        byteArrayFromArray_sameByteRunEnd_pushRepeat data b (i + 1) (out.push b)
      have hs :
          sameByteRunEnd data b i = sameByteRunEnd data b (i + 1) := by
        rw [sameByteRunEnd.eq_def]
        simp [h, heq]
      have hgt : i < sameByteRunEnd data b (i + 1) := by
        have hge : i + 1 ≤ sameByteRunEnd data b (i + 1) := sameByteRunEnd_ge data b (i + 1)
        omega
      have hdiff :
          sameByteRunEnd data b (i + 1) - i =
            (sameByteRunEnd data b (i + 1) - (i + 1)) + 1 := by
        omega
      have hpush :
          pushRepeat out b (sameByteRunEnd data b (i + 1) - i) =
            pushRepeat (out.push b) b (sameByteRunEnd data b (i + 1) - (i + 1)) := by
        have htmp := pushRepeat_push_eq out b (sameByteRunEnd data b (i + 1) - (i + 1))
        -- rewrite both sides to the canonical `pushRepeat out b (_ + 1)` form
        calc
          pushRepeat out b (sameByteRunEnd data b (i + 1) - i)
              = pushRepeat out b ((sameByteRunEnd data b (i + 1) - (i + 1)) + 1) := by
                  simp [hdiff]
          _ = pushRepeat (out.push b) b (sameByteRunEnd data b (i + 1) - (i + 1)) := by
                  simpa using htmp.symm
      rw [byteArrayFromArray_unfold]
      have hdatai : data[i] = b := by simpa using heq
      simp [h, hdatai]
      calc
        byteArrayFromArray data (i + 1) (out.push b)
            = byteArrayFromArray data (sameByteRunEnd data b (i + 1))
                (pushRepeat (out.push b) b (sameByteRunEnd data b (i + 1) - (i + 1))) := hrec
        _ = byteArrayFromArray data (sameByteRunEnd data b (i + 1))
                (pushRepeat out b (sameByteRunEnd data b (i + 1) - i)) := by
              simp [hpush]
        _ = byteArrayFromArray data (sameByteRunEnd data b i)
                (pushRepeat out b (sameByteRunEnd data b i - i)) := by
              rw [← hs]
    · have hs : sameByteRunEnd data b i = i := by
        rw [sameByteRunEnd.eq_def]
        simp [h, heq]
      simpa [hs]
  · have hs : sameByteRunEnd data b i = i := by
      rw [sameByteRunEnd.eq_def]
      simp [h]
    have hba : byteArrayFromArray data i out = out := by
      rw [byteArrayFromArray_unfold]
      simp [h]
    calc
      byteArrayFromArray data i out = out := hba
      _ = byteArrayFromArray data (sameByteRunEnd data b i)
            (pushRepeat out b (sameByteRunEnd data b i - i)) := by
            simpa [hs] using hba.symm

def fixedRunScanBitsEob (data : Array UInt8) (i : Nat) : Nat × Nat :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEnd data b (i + 1)
    let runLen := j - i
    let tail := fixedRunScanBitsEob data j
    if 4 ≤ runLen then
      dist1RunBitsTail b (runLen - 1) tail.1 tail.2
    else
      literalRepeatBitsTail b runLen tail.1 tail.2
  else
    let eob := fixedLitLenCode 256
    (reverseBits eob.1 eob.2, eob.2)
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  let j := sameByteRunEnd data data[i] (i + 1)
  have hgt : i < j := by
    exact sameByteRunEnd_gt_prev data i hlt
  have hle : j ≤ data.size := by
    exact sameByteRunEnd_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  omega

def fixedRunScanStepsEob (data : Array UInt8) (i : Nat) : Nat :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEnd data b (i + 1)
    let runLen := j - i
    let tail := fixedRunScanStepsEob data j
    if 4 ≤ runLen then
      dist1RunSteps (runLen - 1) + tail
    else
      runLen + tail
  else
    1
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  let j := sameByteRunEnd data data[i] (i + 1)
  have hgt : i < j := by
    exact sameByteRunEnd_gt_prev data i hlt
  have hle : j ≤ data.size := by
    exact sameByteRunEnd_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  omega

def fixedRunScanOut (data : Array UInt8) (i : Nat) (out : ByteArray) : ByteArray :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEnd data b (i + 1)
    let runLen := j - i
    let out' :=
      if 4 ≤ runLen then
        dist1RunOut out b (runLen - 1)
      else
        pushRepeat out b runLen
    fixedRunScanOut data j out'
  else
    out
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  let j := sameByteRunEnd data data[i] (i + 1)
  have hgt : i < j := by
    exact sameByteRunEnd_gt_prev data i hlt
  have hle : j ≤ data.size := by
    exact sameByteRunEnd_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  omega

lemma fixedRunScanBitsEob_unfold (data : Array UInt8) (i : Nat) :
    fixedRunScanBitsEob data i =
      (if h : i < data.size then
        let b := data[i]
        let j := sameByteRunEnd data b (i + 1)
        let runLen := j - i
        let tail := fixedRunScanBitsEob data j
        if 4 ≤ runLen then
          dist1RunBitsTail b (runLen - 1) tail.1 tail.2
        else
          literalRepeatBitsTail b runLen tail.1 tail.2
      else
        let eob := fixedLitLenCode 256
        (reverseBits eob.1 eob.2, eob.2)) := by
  exact fixedRunScanBitsEob.eq_1 (data := data) (i := i)

lemma fixedRunScanStepsEob_unfold (data : Array UInt8) (i : Nat) :
    fixedRunScanStepsEob data i =
      (if h : i < data.size then
        let b := data[i]
        let j := sameByteRunEnd data b (i + 1)
        let runLen := j - i
        let tail := fixedRunScanStepsEob data j
        if 4 ≤ runLen then
          dist1RunSteps (runLen - 1) + tail
        else
          runLen + tail
      else
        1) := by
  exact fixedRunScanStepsEob.eq_1 (data := data) (i := i)

lemma fixedRunScanOut_unfold (data : Array UInt8) (i : Nat) (out : ByteArray) :
    fixedRunScanOut data i out =
      (if h : i < data.size then
        let b := data[i]
        let j := sameByteRunEnd data b (i + 1)
        let runLen := j - i
        let out' :=
          if 4 ≤ runLen then
            dist1RunOut out b (runLen - 1)
          else
            pushRepeat out b runLen
        fixedRunScanOut data j out'
      else
        out) := by
  exact fixedRunScanOut.eq_1 (data := data) (i := i) (out := out)

lemma fixedRunScanOut_eq_byteArrayFromArray (data : Array UInt8) (i : Nat) (out : ByteArray) :
    fixedRunScanOut data i out = byteArrayFromArray data i out := by
  classical
  rw [fixedRunScanOut.eq_1]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    let j := sameByteRunEnd data b (i + 1)
    let runLen := j - i
    have hnext : sameByteRunEnd data data[i] (i + 1) = j := by
      simpa [b, j]
    have hrun : sameByteRunEnd data data[i] (i + 1) - i = runLen := by
      simpa [b, j, runLen]
    have hscan0 : sameByteRunEnd data b i = j := by
      rw [sameByteRunEnd.eq_def]
      simp [hlt, b, hnext]
    have hbaRun :
        byteArrayFromArray data i out =
          byteArrayFromArray data j (pushRepeat out b runLen) := by
      have htmp := byteArrayFromArray_sameByteRunEnd_pushRepeat data b i out
      simpa [j, runLen, hscan0] using htmp
    by_cases h4 : 4 ≤ runLen
    · have hih :
          fixedRunScanOut data j (dist1RunOut out b (runLen - 1)) =
            byteArrayFromArray data j (dist1RunOut out b (runLen - 1)) := by
          exact fixedRunScanOut_eq_byteArrayFromArray data j (dist1RunOut out b (runLen - 1))
      have hgt : i < j := by
        dsimp [j, b]
        exact sameByteRunEnd_gt_prev data i hlt
      have hrunPos : 0 < runLen := by
        dsimp [runLen]
        omega
      have haccEq : dist1RunOut out b (runLen - 1) = pushRepeat out b runLen := by
        have htmp := dist1RunOut_eq_pushRepeat out b (runLen - 1)
        have harrith : (runLen - 1) + 1 = runLen := by
          omega
        simpa [harrith] using htmp
      have hmid :
          fixedRunScanOut data j (dist1RunOut out b (runLen - 1)) =
            byteArrayFromArray data i out := by
        refine hih.trans ?_
        calc
          byteArrayFromArray data j (dist1RunOut out b (runLen - 1))
              = byteArrayFromArray data j (pushRepeat out b runLen) := by
                  simp [haccEq]
          _ = byteArrayFromArray data i out := hbaRun.symm
      simpa [b, j, runLen, hnext, hrun, h4] using hmid
    · have hih :
          fixedRunScanOut data j (pushRepeat out b runLen) =
            byteArrayFromArray data j (pushRepeat out b runLen) := by
          exact fixedRunScanOut_eq_byteArrayFromArray data j (pushRepeat out b runLen)
      simpa [b, j, runLen, hnext, hrun, h4] using hih.trans hbaRun.symm
  · rw [byteArrayFromArray_unfold]
    simp [hlt]
termination_by data.size - i
decreasing_by
  all_goals
    have hlt' : i < data.size := hlt
    have hgt : i < sameByteRunEnd data data[i] (i + 1) := by
      exact sameByteRunEnd_gt_prev data i hlt'
    have hle : sameByteRunEnd data data[i] (i + 1) ≤ data.size := by
      exact sameByteRunEnd_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt')
    omega

def quadTailEqb (data : Array UInt8) (i : Nat) (b : UInt8) (h3 : i + 3 < data.size) : Bool :=
  let b1 := data[i + 1]'(by omega)
  let b2 := data[i + 2]'(by omega)
  let b3 := data[i + 3]'h3
  (b1 == b) && (b2 == b) && (b3 == b)

lemma quadTailEqb_eq_true
    (data : Array UInt8) (i : Nat) (b : UInt8) (h3 : i + 3 < data.size) :
    quadTailEqb data i b h3 = true ↔
      data[i + 1]'(by omega) = b ∧
      data[i + 2]'(by omega) = b ∧
      data[i + 3]'h3 = b := by
  unfold quadTailEqb
  simp [Bool.and_eq_true, and_assoc]

def fixedQuadBitsEob (data : Array UInt8) (i : Nat) : Nat × Nat :=
  if h : i < data.size then
    let b := data[i]
    if h3 : i + 3 < data.size then
      if quadTailEqb data i b h3 then
        let tail := fixedQuadBitsEob data (i + 4)
        dist1RunBitsTail b 3 tail.1 tail.2
      else
        let tail := fixedQuadBitsEob data (i + 1)
        literalRepeatBitsTail b 1 tail.1 tail.2
    else
      let tail := fixedQuadBitsEob data (i + 1)
      literalRepeatBitsTail b 1 tail.1 tail.2
  else
    let eob := fixedLitLenCode 256
    (reverseBits eob.1 eob.2, eob.2)
termination_by data.size - i
decreasing_by
  · have hle : data.size - (i + 4) < data.size - i := by
      omega
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle

def fixedQuadStepsEob (data : Array UInt8) (i : Nat) : Nat :=
  if h : i < data.size then
    let b := data[i]
    if h3 : i + 3 < data.size then
      if quadTailEqb data i b h3 then
        dist1RunSteps 3 + fixedQuadStepsEob data (i + 4)
      else
        1 + fixedQuadStepsEob data (i + 1)
    else
      1 + fixedQuadStepsEob data (i + 1)
  else
    1
termination_by data.size - i
decreasing_by
  · have hle : data.size - (i + 4) < data.size - i := by
      omega
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle

def fixedQuadOut (data : Array UInt8) (i : Nat) (out : ByteArray) : ByteArray :=
  if h : i < data.size then
    let b := data[i]
    if h3 : i + 3 < data.size then
      if quadTailEqb data i b h3 then
        fixedQuadOut data (i + 4) (dist1RunOut out b 3)
      else
        fixedQuadOut data (i + 1) (out.push b)
    else
      fixedQuadOut data (i + 1) (out.push b)
  else
    out
termination_by data.size - i
decreasing_by
  · have hle : data.size - (i + 4) < data.size - i := by
      omega
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle

lemma fixedQuadBitsEob_unfold (data : Array UInt8) (i : Nat) :
    fixedQuadBitsEob data i =
      (if h : i < data.size then
        let b := data[i]
        if h3 : i + 3 < data.size then
          if quadTailEqb data i b h3 then
            let tail := fixedQuadBitsEob data (i + 4)
            dist1RunBitsTail b 3 tail.1 tail.2
          else
            let tail := fixedQuadBitsEob data (i + 1)
            literalRepeatBitsTail b 1 tail.1 tail.2
        else
          let tail := fixedQuadBitsEob data (i + 1)
          literalRepeatBitsTail b 1 tail.1 tail.2
      else
        let eob := fixedLitLenCode 256
        (reverseBits eob.1 eob.2, eob.2)) := by
  exact fixedQuadBitsEob.eq_1 (data := data) (i := i)

lemma fixedQuadStepsEob_unfold (data : Array UInt8) (i : Nat) :
    fixedQuadStepsEob data i =
      (if h : i < data.size then
        let b := data[i]
        if h3 : i + 3 < data.size then
          if quadTailEqb data i b h3 then
            dist1RunSteps 3 + fixedQuadStepsEob data (i + 4)
          else
            1 + fixedQuadStepsEob data (i + 1)
        else
          1 + fixedQuadStepsEob data (i + 1)
      else
        1) := by
  exact fixedQuadStepsEob.eq_1 (data := data) (i := i)

lemma fixedQuadOut_unfold (data : Array UInt8) (i : Nat) (out : ByteArray) :
    fixedQuadOut data i out =
      (if h : i < data.size then
        let b := data[i]
        if h3 : i + 3 < data.size then
          if quadTailEqb data i b h3 then
            fixedQuadOut data (i + 4) (dist1RunOut out b 3)
          else
            fixedQuadOut data (i + 1) (out.push b)
        else
          fixedQuadOut data (i + 1) (out.push b)
      else
        out) := by
  exact fixedQuadOut.eq_1 (data := data) (i := i) (out := out)

lemma dist1RunBitsTail_len_ge (b : UInt8) (remaining tailBits tailLen : Nat) :
    tailLen ≤ (dist1RunBitsTail b remaining tailBits tailLen).2 := by
  unfold dist1RunBitsTail
  let remLit := dist1ChunkLoopRem remaining
  let litTail := literalRepeatBitsTail b remLit tailBits tailLen
  let chunkBits := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
  let codeLen := fixedLitLenCode b.toNat
  have hlit : tailLen ≤ litTail.2 := by
    dsimp [litTail]
    exact literalRepeatBitsTail_len_ge b remLit tailBits tailLen
  have hchunk : litTail.2 ≤ chunkBits.2 := by
    dsimp [chunkBits]
    exact dist1ChunkLoopBitsTail_len_ge remaining litTail.1 litTail.2
  have hcode : chunkBits.2 ≤ codeLen.2 + chunkBits.2 := Nat.le_add_left _ _
  exact le_trans hlit (le_trans hchunk hcode)

lemma dist1RunBitsTail_len_ge_two
    (b : UInt8) (remaining tailBits tailLen : Nat) (htail2 : 2 ≤ tailLen) :
    2 ≤ (dist1RunBitsTail b remaining tailBits tailLen).2 := by
  exact le_trans htail2 (dist1RunBitsTail_len_ge b remaining tailBits tailLen)

lemma fixedRunScanBitsEob_len_ge_two (data : Array UInt8) (i : Nat) :
    2 ≤ (fixedRunScanBitsEob data i).2 := by
  classical
  rw [fixedRunScanBitsEob.eq_1]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    let j := sameByteRunEnd data b (i + 1)
    let runLen := j - i
    have htail : 2 ≤ (fixedRunScanBitsEob data j).2 := by
      exact fixedRunScanBitsEob_len_ge_two data j
    by_cases h4 : 4 ≤ runLen
    · simpa [b, j, runLen, h4] using
        (dist1RunBitsTail_len_ge_two b (runLen - 1) (fixedRunScanBitsEob data j).1
          (fixedRunScanBitsEob data j).2 htail)
    · simpa [b, j, runLen, h4] using
        (literalRepeatBitsTail_len_ge_two b runLen (fixedRunScanBitsEob data j).1
          (fixedRunScanBitsEob data j).2 htail)
  · simp [hlt, fixedLitLenCode]
termination_by data.size - i
decreasing_by
  have hlt' : i < data.size := hlt
  have hgt : i < sameByteRunEnd data data[i] (i + 1) := by
    exact sameByteRunEnd_gt_prev data i hlt'
  have hle : sameByteRunEnd data data[i] (i + 1) ≤ data.size := by
    exact sameByteRunEnd_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt')
  omega

lemma fixedQuadBitsEob_len_ge_two (data : Array UInt8) (i : Nat) :
    2 ≤ (fixedQuadBitsEob data i).2 := by
  classical
  rw [fixedQuadBitsEob_unfold]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    by_cases h3 : i + 3 < data.size
    · dsimp [b]
      by_cases hq : quadTailEqb data i b h3 = true
      · have htail : 2 ≤ (fixedQuadBitsEob data (i + 4)).2 := by
          exact fixedQuadBitsEob_len_ge_two data (i + 4)
        simpa [b, h3, hq] using
          (dist1RunBitsTail_len_ge_two b 3 (fixedQuadBitsEob data (i + 4)).1
            (fixedQuadBitsEob data (i + 4)).2 htail)
      · have htail : 2 ≤ (fixedQuadBitsEob data (i + 1)).2 := by
          exact fixedQuadBitsEob_len_ge_two data (i + 1)
        simpa [b, h3, hq] using
          (literalRepeatBitsTail_len_ge_two b 1 (fixedQuadBitsEob data (i + 1)).1
            (fixedQuadBitsEob data (i + 1)).2 htail)
    · dsimp [b]
      have htail : 2 ≤ (fixedQuadBitsEob data (i + 1)).2 := by
        exact fixedQuadBitsEob_len_ge_two data (i + 1)
      simpa [b, h3] using
        (literalRepeatBitsTail_len_ge_two b 1 (fixedQuadBitsEob data (i + 1)).1
          (fixedQuadBitsEob data (i + 1)).2 htail)
  · simp [hlt, fixedLitLenCode]
termination_by data.size - i
decreasing_by
  all_goals omega

def fixedQuadBitsTail (data : Array UInt8) (i tailBits tailLen : Nat) : Nat × Nat :=
  if h : i < data.size then
    let b := data[i]
    if h3 : i + 3 < data.size then
      if quadTailEqb data i b h3 then
        let tail := fixedQuadBitsTail data (i + 4) tailBits tailLen
        dist1RunBitsTail b 3 tail.1 tail.2
      else
        let tail := fixedQuadBitsTail data (i + 1) tailBits tailLen
        literalRepeatBitsTail b 1 tail.1 tail.2
    else
      let tail := fixedQuadBitsTail data (i + 1) tailBits tailLen
      literalRepeatBitsTail b 1 tail.1 tail.2
  else
    let eob := fixedLitLenCode 256
    (reverseBits eob.1 eob.2 ||| (tailBits <<< eob.2), eob.2 + tailLen)
termination_by data.size - i
decreasing_by
  · have hle : data.size - (i + 4) < data.size - i := by
      omega
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle

lemma fixedQuadBitsTail_unfold (data : Array UInt8) (i tailBits tailLen : Nat) :
    fixedQuadBitsTail data i tailBits tailLen =
      (if h : i < data.size then
        let b := data[i]
        if h3 : i + 3 < data.size then
          if quadTailEqb data i b h3 then
            let tail := fixedQuadBitsTail data (i + 4) tailBits tailLen
            dist1RunBitsTail b 3 tail.1 tail.2
          else
            let tail := fixedQuadBitsTail data (i + 1) tailBits tailLen
            literalRepeatBitsTail b 1 tail.1 tail.2
        else
          let tail := fixedQuadBitsTail data (i + 1) tailBits tailLen
          literalRepeatBitsTail b 1 tail.1 tail.2
      else
        let eob := fixedLitLenCode 256
        (reverseBits eob.1 eob.2 ||| (tailBits <<< eob.2), eob.2 + tailLen)) := by
  exact fixedQuadBitsTail.eq_1 (data := data) (i := i) (tailBits := tailBits) (tailLen := tailLen)

lemma fixedQuadBitsTail_len_ge (data : Array UInt8) (i tailBits tailLen : Nat) :
    tailLen ≤ (fixedQuadBitsTail data i tailBits tailLen).2 := by
  classical
  rw [fixedQuadBitsTail_unfold]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    by_cases h3 : i + 3 < data.size
    · dsimp [b]
      by_cases hq : quadTailEqb data i b h3 = true
      · have htail : tailLen ≤ (fixedQuadBitsTail data (i + 4) tailBits tailLen).2 := by
          exact fixedQuadBitsTail_len_ge data (i + 4) tailBits tailLen
        have hmore :
            (fixedQuadBitsTail data (i + 4) tailBits tailLen).2 ≤
              (dist1RunBitsTail b 3 (fixedQuadBitsTail data (i + 4) tailBits tailLen).1
                (fixedQuadBitsTail data (i + 4) tailBits tailLen).2).2 := by
          exact dist1RunBitsTail_len_ge b 3 (fixedQuadBitsTail data (i + 4) tailBits tailLen).1
            (fixedQuadBitsTail data (i + 4) tailBits tailLen).2
        exact le_trans htail (by simpa [b, h3, hq] using hmore)
      · have htail : tailLen ≤ (fixedQuadBitsTail data (i + 1) tailBits tailLen).2 := by
          exact fixedQuadBitsTail_len_ge data (i + 1) tailBits tailLen
        have hmore :
            (fixedQuadBitsTail data (i + 1) tailBits tailLen).2 ≤
              (literalRepeatBitsTail b 1 (fixedQuadBitsTail data (i + 1) tailBits tailLen).1
                (fixedQuadBitsTail data (i + 1) tailBits tailLen).2).2 := by
          exact literalRepeatBitsTail_len_ge b 1 (fixedQuadBitsTail data (i + 1) tailBits tailLen).1
            (fixedQuadBitsTail data (i + 1) tailBits tailLen).2
        exact le_trans htail (by simpa [b, h3, hq] using hmore)
    · dsimp [b]
      have htail : tailLen ≤ (fixedQuadBitsTail data (i + 1) tailBits tailLen).2 := by
        exact fixedQuadBitsTail_len_ge data (i + 1) tailBits tailLen
      have hmore :
          (fixedQuadBitsTail data (i + 1) tailBits tailLen).2 ≤
            (literalRepeatBitsTail b 1 (fixedQuadBitsTail data (i + 1) tailBits tailLen).1
              (fixedQuadBitsTail data (i + 1) tailBits tailLen).2).2 := by
        exact literalRepeatBitsTail_len_ge b 1 (fixedQuadBitsTail data (i + 1) tailBits tailLen).1
          (fixedQuadBitsTail data (i + 1) tailBits tailLen).2
      exact le_trans htail (by simpa [b, h3] using hmore)
  · simp [hlt, fixedLitLenCode, Nat.le_add_left]
termination_by data.size - i
decreasing_by
  all_goals omega

lemma fixedQuadBitsTail_len_ge_two
    (data : Array UInt8) (i tailBits tailLen : Nat) (htail2 : 2 ≤ tailLen) :
    2 ≤ (fixedQuadBitsTail data i tailBits tailLen).2 := by
  exact le_trans htail2 (fixedQuadBitsTail_len_ge data i tailBits tailLen)

lemma byteArrayFromArray_quad4_eq_dist1RunOut
    (data : Array UInt8) (i : Nat) (out : ByteArray)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = true) :
    byteArrayFromArray data i out =
      byteArrayFromArray data (i + 4) (dist1RunOut out data[i] 3) := by
  have h1 : i + 1 < data.size := by omega
  have h2 : i + 2 < data.size := by omega
  have hq' := (quadTailEqb_eq_true (data := data) (i := i) (b := data[i]) (h3 := h3)).1 hq
  have hb1 : data[i + 1]'(by omega) = data[i] := hq'.1
  have hb2 : data[i + 2]'(by omega) = data[i] := hq'.2.1
  have hb3 : data[i + 3]'h3 = data[i] := hq'.2.2
  have hb1' : data[i + 1] = data[i] := by
    simpa using hb1
  have hb2' : data[i + 2] = data[i] := by
    simpa using hb2
  have hb3' : data[i + 3] = data[i] := by
    simpa using hb3
  rw [byteArrayFromArray_unfold]
  simp [h]
  rw [byteArrayFromArray_unfold]
  simp [h1, hb1']
  rw [byteArrayFromArray_unfold]
  simp [h2, hb2']
  rw [byteArrayFromArray_unfold]
  simp [h3, hb3', dist1RunOut, pushRepeat]

lemma fixedQuadOut_eq_byteArrayFromArray (data : Array UInt8) (i : Nat) (out : ByteArray) :
    fixedQuadOut data i out = byteArrayFromArray data i out := by
  classical
  rw [fixedQuadOut_unfold, byteArrayFromArray_unfold]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    by_cases h3 : i + 3 < data.size
    · dsimp [b]
      by_cases hq : quadTailEqb data i b h3 = true
      · have hih : fixedQuadOut data (i + 4) (dist1RunOut out b 3) =
            byteArrayFromArray data (i + 4) (dist1RunOut out b 3) := by
            exact fixedQuadOut_eq_byteArrayFromArray data (i + 4) (dist1RunOut out b 3)
        have hquad :
            byteArrayFromArray data i out =
              byteArrayFromArray data (i + 4) (dist1RunOut out b 3) := by
          simpa [b] using
            (byteArrayFromArray_quad4_eq_dist1RunOut (data := data) (i := i) (out := out)
              (h := hlt) (h3 := h3) (hq := by simpa [b] using hq))
        have hquad1 :
            byteArrayFromArray data (i + 1) (out.push b) =
              byteArrayFromArray data (i + 4) (dist1RunOut out b 3) := by
          have htmp : byteArrayFromArray data (i + 1) (out.push b) = byteArrayFromArray data i out := by
            symm
            rw [byteArrayFromArray_unfold]
            simp [hlt, b]
          exact htmp.trans hquad
        simpa [b, h3, hq, hquad1] using hih
      · have hih : fixedQuadOut data (i + 1) (out.push b) =
            byteArrayFromArray data (i + 1) (out.push b) := by
            exact fixedQuadOut_eq_byteArrayFromArray data (i + 1) (out.push b)
        simpa [b, h3, hq] using hih
    · dsimp [b]
      have hih : fixedQuadOut data (i + 1) (out.push b) =
          byteArrayFromArray data (i + 1) (out.push b) := by
          exact fixedQuadOut_eq_byteArrayFromArray data (i + 1) (out.push b)
      simpa [b, h3] using hih
  · simp [hlt]
termination_by data.size - i
decreasing_by
  all_goals omega

lemma fixedQuadOut_empty (data : Array UInt8) :
    fixedQuadOut data 0 ByteArray.empty = ByteArray.mk data := by
  calc
    fixedQuadOut data 0 ByteArray.empty = byteArrayFromArray data 0 ByteArray.empty := by
      simpa using fixedQuadOut_eq_byteArrayFromArray data 0 ByteArray.empty
    _ = ByteArray.mk data := by
      simpa using byteArrayFromArray_empty (data := data)

lemma fixedQuadBitsTail_zero_zero (data : Array UInt8) (i : Nat) :
    fixedQuadBitsTail data i 0 0 = fixedQuadBitsEob data i := by
  classical
  rw [fixedQuadBitsTail_unfold, fixedQuadBitsEob_unfold]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    by_cases h3 : i + 3 < data.size
    · dsimp [b]
      by_cases hq : quadTailEqb data i b h3 = true
      · simpa [b, h3, hq, fixedQuadBitsTail_zero_zero data (i + 4)]
      · simpa [b, h3, hq, fixedQuadBitsTail_zero_zero data (i + 1)]
    · dsimp [b]
      simpa [b, h3, fixedQuadBitsTail_zero_zero data (i + 1)]
  · simp [hlt, fixedLitLenCode]
termination_by data.size - i
decreasing_by
  all_goals omega

lemma fixedQuadBitsEob_of_quad
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = true) :
    fixedQuadBitsEob data i =
      dist1RunBitsTail data[i] 3 (fixedQuadBitsEob data (i + 4)).1 (fixedQuadBitsEob data (i + 4)).2 := by
  rw [fixedQuadBitsEob_unfold]
  simp [h, h3, hq]

lemma fixedQuadStepsEob_of_quad
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = true) :
    fixedQuadStepsEob data i = dist1RunSteps 3 + fixedQuadStepsEob data (i + 4) := by
  rw [fixedQuadStepsEob_unfold]
  simp [h, h3, hq]

lemma fixedQuadOut_of_quad
    (data : Array UInt8) (i : Nat) (out : ByteArray)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = true) :
    fixedQuadOut data i out = fixedQuadOut data (i + 4) (dist1RunOut out data[i] 3) := by
  rw [fixedQuadOut_unfold]
  simp [h, h3, hq]

lemma fixedQuadBitsEob_of_lit_hqFalse
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = false) :
    fixedQuadBitsEob data i =
      literalRepeatBitsTail data[i] 1 (fixedQuadBitsEob data (i + 1)).1 (fixedQuadBitsEob data (i + 1)).2 := by
  rw [fixedQuadBitsEob_unfold]
  simp [h, h3, hq]

lemma fixedQuadStepsEob_of_lit_hqFalse
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = false) :
    fixedQuadStepsEob data i = 1 + fixedQuadStepsEob data (i + 1) := by
  rw [fixedQuadStepsEob_unfold]
  simp [h, h3, hq]

lemma fixedQuadOut_of_lit_hqFalse
    (data : Array UInt8) (i : Nat) (out : ByteArray)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = false) :
    fixedQuadOut data i out = fixedQuadOut data (i + 1) (out.push data[i]) := by
  rw [fixedQuadOut_unfold]
  simp [h, h3, hq]

lemma fixedQuadBitsEob_of_lit_noh3
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : ¬ i + 3 < data.size) :
    fixedQuadBitsEob data i =
      literalRepeatBitsTail data[i] 1 (fixedQuadBitsEob data (i + 1)).1 (fixedQuadBitsEob data (i + 1)).2 := by
  rw [fixedQuadBitsEob_unfold]
  simp [h, h3]

lemma fixedQuadStepsEob_of_lit_noh3
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : ¬ i + 3 < data.size) :
    fixedQuadStepsEob data i = 1 + fixedQuadStepsEob data (i + 1) := by
  rw [fixedQuadStepsEob_unfold]
  simp [h, h3]

lemma fixedQuadOut_of_lit_noh3
    (data : Array UInt8) (i : Nat) (out : ByteArray)
    (h : i < data.size) (h3 : ¬ i + 3 < data.size) :
    fixedQuadOut data i out = fixedQuadOut data (i + 1) (out.push data[i]) := by
  rw [fixedQuadOut_unfold]
  simp [h, h3]

end Png
end Bitmaps
