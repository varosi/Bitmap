import Bitmap.Lemmas.Png.DynamicEncoderDecode
import Bitmap.Lemmas.Png.DynamicBlockProofsPayload

namespace Bitmaps

namespace Lemmas

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-- Bit reversal is injective inside a fixed-width code space. This prevents
later generated Huffman-table fills from overwriting an earlier row entry. -/
lemma reverseBits_injective_of_lt
    {a b len : Nat} (ha : a < 2 ^ len) (hb : b < 2 ^ len)
    (h : Png.reverseBits a len = Png.reverseBits b len) :
    a = b := by
  calc
    a = Png.reverseBits (Png.reverseBits a len) len := by
          exact (Png.reverseBits_reverseBits a len ha).symm
    _ = Png.reverseBits (Png.reverseBits b len) len := by rw [h]
    _ = b := Png.reverseBits_reverseBits b len hb

/-- Huffman table filling preserves the number of decode rows when it succeeds.
Generated payload decoding uses this to recover concrete row bounds from
`mkHuffman` without unfolding every successful table fill. -/
lemma fillHuffmanTableAux_size_of_some
    (lengths : Array Nat) (i : Nat) (nextCode : Array Nat)
    (table out : Array (Array (Option Nat)))
    (hfill :
      Png.fillHuffmanTableAux lengths i nextCode table = some out) :
    out.size = table.size := by
  rw [Png.fillHuffmanTableAux.eq_1] at hfill
  by_cases hi : i < lengths.size
  · by_cases hlen : lengths[i] > 0
    · let codeVal := nextCode[lengths[i]]!
      by_cases hcode : codeVal >= (1 <<< lengths[i])
      · simp [hi, hlen, codeVal, hcode] at hfill
      · let nextCode' := nextCode.set! lengths[i] (codeVal + 1)
        let rev := Png.reverseBits codeVal lengths[i]
        let row := table[lengths[i]]!
        by_cases hrev : rev >= row.size
        · simp [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev] at hfill
        · let row' := row.set! rev (some i)
          let table' := table.set! lengths[i] row'
          have hfillRec :
              Png.fillHuffmanTableAux lengths (i + 1) nextCode' table' =
                some out := by
            simpa [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev,
              row', table'] using hfill
          have hrec :=
            fillHuffmanTableAux_size_of_some lengths (i + 1) nextCode'
              table' out hfillRec
          calc
            out.size = table'.size := hrec
            _ = table.size := by simp [table']
    · have hrec :=
        fillHuffmanTableAux_size_of_some lengths (i + 1) nextCode table out
          (by simpa [hi, hlen] using hfill)
      exact hrec
  · have hout : table = out := by
      simpa [hi] using hfill
    rw [← hout]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Successful Huffman table filling preserves the width of any existing row.
Generated payload decoding uses this to recover the concrete lookup-row size
after the builder has installed symbol entries. -/
lemma fillHuffmanTableAux_row_size_of_some
    (lengths : Array Nat) (i : Nat) (nextCode : Array Nat)
    (table out : Array (Array (Option Nat))) (rowIdx : Nat)
    (hrow : rowIdx < table.size)
    (hfill :
      Png.fillHuffmanTableAux lengths i nextCode table = some out) :
    out[rowIdx]!.size = table[rowIdx]!.size := by
  rw [Png.fillHuffmanTableAux.eq_1] at hfill
  by_cases hi : i < lengths.size
  · by_cases hlen : lengths[i] > 0
    · let codeVal := nextCode[lengths[i]]!
      by_cases hcode : codeVal >= (1 <<< lengths[i])
      · simp [hi, hlen, codeVal, hcode] at hfill
      · let nextCode' := nextCode.set! lengths[i] (codeVal + 1)
        let rev := Png.reverseBits codeVal lengths[i]
        let row := table[lengths[i]]!
        by_cases hrev : rev >= row.size
        · simp [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev] at hfill
        · let row' := row.set! rev (some i)
          let table' := table.set! lengths[i] row'
          have hfillRec :
              Png.fillHuffmanTableAux lengths (i + 1) nextCode' table' =
                some out := by
            simpa [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev,
              row', table'] using hfill
          have hrow' : rowIdx < table'.size := by
            simpa [table'] using hrow
          have hrec :=
            fillHuffmanTableAux_row_size_of_some lengths (i + 1) nextCode'
              table' out rowIdx hrow' hfillRec
          have htable' : table'[rowIdx]!.size = table[rowIdx]!.size := by
            by_cases heq : lengths[i] = rowIdx
            · subst rowIdx
              simp [table', row', row, hrow]
            · have hset : table'[rowIdx]! = table[rowIdx]! := by
                simpa [table'] using
                  getElem!_set!_ne table (lengths[i]) rowIdx row' hrow heq
              simpa [hset]
          exact hrec.trans htable'
    · have hrec :=
        fillHuffmanTableAux_row_size_of_some lengths (i + 1) nextCode table out
          rowIdx hrow (by simpa [hi, hlen] using hfill)
      exact hrec
  · have hout : table = out := by
      simpa [hi] using hfill
    rw [← hout]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Uniform Huffman table filling leaves rows other than the uniform code-length
row unchanged. Generated payload decoding uses this to show shorter prefix rows
cannot resolve before the nine-bit literal/length row. -/
lemma fillHuffmanTableAux_uniform_row_eq_of_ne
    (lengths : Array Nat) (i codeLen : Nat) (nextCode : Array Nat)
    (table out : Array (Array (Option Nat))) (rowIdx : Nat)
    (hshape :
      ∀ j (hj : j < lengths.size), i ≤ j →
        0 < lengths[j] → lengths[j] = codeLen)
    (hrowNe : rowIdx ≠ codeLen)
    (hrow : rowIdx < table.size)
    (hfill :
      Png.fillHuffmanTableAux lengths i nextCode table = some out) :
    out[rowIdx]! = table[rowIdx]! := by
  rw [Png.fillHuffmanTableAux.eq_1] at hfill
  by_cases hi : i < lengths.size
  · by_cases hlen : lengths[i] > 0
    · have hlenEq : lengths[i] = codeLen :=
        hshape i hi le_rfl hlen
      let codeVal := nextCode[lengths[i]]!
      by_cases hcode : codeVal >= (1 <<< lengths[i])
      · simp [hi, hlen, codeVal, hcode] at hfill
      · let nextCode' := nextCode.set! lengths[i] (codeVal + 1)
        let rev := Png.reverseBits codeVal lengths[i]
        let row := table[lengths[i]]!
        by_cases hrev : rev >= row.size
        · simp [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev] at hfill
        · let row' := row.set! rev (some i)
          let table' := table.set! lengths[i] row'
          have hfillRec :
              Png.fillHuffmanTableAux lengths (i + 1) nextCode' table' =
                some out := by
            simpa [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev,
              row', table'] using hfill
          have hrow' : rowIdx < table'.size := by
            simpa [table'] using hrow
          have hshape' :
              ∀ j (hj : j < lengths.size), i + 1 ≤ j →
                0 < lengths[j] → lengths[j] = codeLen := by
            intro j hj hle hpos
            exact hshape j hj (by omega) hpos
          have hrec :=
            fillHuffmanTableAux_uniform_row_eq_of_ne lengths (i + 1) codeLen
              nextCode' table' out rowIdx hshape' hrowNe hrow' hfillRec
          have hset : table'[rowIdx]! = table[rowIdx]! := by
            have hne : lengths[i] ≠ rowIdx := by
              intro heq
              exact hrowNe (heq ▸ hlenEq)
            simpa [table'] using
              getElem!_set!_ne table (lengths[i]) rowIdx row' hrow hne
          exact hrec.trans hset
    · have hshape' :
        ∀ j (hj : j < lengths.size), i + 1 ≤ j →
          0 < lengths[j] → lengths[j] = codeLen := by
        intro j hj hle hpos
        exact hshape j hj (by omega) hpos
      have hrec :=
        fillHuffmanTableAux_uniform_row_eq_of_ne lengths (i + 1) codeLen
          nextCode table out rowIdx hshape' hrowNe hrow
          (by simpa [hi, hlen] using hfill)
      exact hrec
  · have hout : table = out := by
      simpa [hi] using hfill
    rw [← hout]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Later uniform Huffman fills cannot overwrite a row entry whose canonical
code is below the current next-code counter. This is the no-overwrite half of
generated payload row-nine lookup. -/
lemma fillHuffmanTableAux_uniform_entry_eq_of_code_lt_next
    (lengths : Array Nat) (i codeLen : Nat) (nextCode : Array Nat)
    (table out : Array (Array (Option Nat))) (targetCode codeIdx : Nat)
    (hshape :
      ∀ j (hj : j < lengths.size), i ≤ j →
        0 < lengths[j] → lengths[j] = codeLen)
    (hnextIdx : codeLen < nextCode.size)
    (htableIdx : codeLen < table.size)
    (hrow : table[codeLen]!.size = 1 <<< codeLen)
    (hbudget : nextCode[codeLen]! + (lengths.size - i) ≤ 1 <<< codeLen)
    (htargetLt : targetCode < nextCode[codeLen]!)
    (hcodeIdx : codeIdx = Png.reverseBits targetCode codeLen)
    (hfill :
      Png.fillHuffmanTableAux lengths i nextCode table = some out) :
    out[codeLen]![codeIdx]! = table[codeLen]![codeIdx]! := by
  rw [Png.fillHuffmanTableAux.eq_1] at hfill
  have htargetSpace : targetCode < 1 <<< codeLen := by omega
  have hcodeIdxBound : codeIdx < table[codeLen]!.size := by
    rw [hrow, hcodeIdx]
    simpa [Nat.shiftLeft_eq] using Png.reverseBits_lt targetCode codeLen
  by_cases hi : i < lengths.size
  · by_cases hpos : 0 < lengths[i]
    · have hlen : lengths[i] = codeLen := hshape i hi le_rfl hpos
      have hcodeLenPos : 0 < codeLen := by
        simpa [hlen] using hpos
      have hremainingPos : 0 < lengths.size - i := by omega
      let codeVal := nextCode[codeLen]!
      have hcodeValLt : codeVal < 1 <<< codeLen := by
        dsimp [codeVal]
        omega
      have hnotCodeGe : ¬ codeVal >= (1 <<< codeLen) := by omega
      let nextCode' := nextCode.set! codeLen (codeVal + 1)
      let rev := Png.reverseBits codeVal codeLen
      let row := table[codeLen]!
      have hrev : rev < row.size := by
        rw [hrow]
        simpa [rev, row, Nat.shiftLeft_eq] using
          Png.reverseBits_lt codeVal codeLen
      have hnotRevGe : ¬ rev >= row.size := by omega
      let row' := row.set! rev (some i)
      let table' := table.set! codeLen row'
      have hfillRec :
          Png.fillHuffmanTableAux lengths (i + 1) nextCode' table' =
            some out := by
        simpa [hi, hpos, hlen, codeVal, hnotCodeGe, nextCode', rev, row,
          hnotRevGe, row', table', hcodeLenPos] using hfill
      have hnextIdx' : codeLen < nextCode'.size := by
        simp [nextCode', hnextIdx]
      have htableIdx' : codeLen < table'.size := by
        simp [table', htableIdx]
      have hnextAt :
          nextCode'[codeLen]! = codeVal + 1 := by
        simpa [nextCode'] using
          getElem!_set!_eq nextCode codeLen (codeVal + 1) hnextIdx
      have hrowSet : table'[codeLen]! = row' := by
        simpa [table'] using getElem!_set!_eq table codeLen row' htableIdx
      have hrow' : table'[codeLen]!.size = 1 <<< codeLen := by
        rw [hrowSet]
        simp [row', row, hrow]
      have hbudget' :
          nextCode'[codeLen]! + (lengths.size - (i + 1)) ≤ 1 <<< codeLen := by
        rw [hnextAt]
        omega
      have htargetLt' : targetCode < nextCode'[codeLen]! := by
        rw [hnextAt]
        omega
      have hshape' :
          ∀ j (hj : j < lengths.size), i + 1 ≤ j →
            0 < lengths[j] → lengths[j] = codeLen := by
        intro j hj hle hposj
        exact hshape j hj (by omega) hposj
      have hrec :=
        fillHuffmanTableAux_uniform_entry_eq_of_code_lt_next
          lengths (i + 1) codeLen nextCode' table' out targetCode codeIdx
          hshape' hnextIdx' htableIdx' hrow' hbudget' htargetLt' hcodeIdx
          hfillRec
      have hne : rev ≠ codeIdx := by
        intro heq
        have hrevEq :
            Png.reverseBits codeVal codeLen =
              Png.reverseBits targetCode codeLen := by
          simpa [rev, hcodeIdx] using heq
        have hcodeValPow : codeVal < 2 ^ codeLen := by
          simpa [Nat.shiftLeft_eq] using hcodeValLt
        have htargetPow : targetCode < 2 ^ codeLen := by
          simpa [Nat.shiftLeft_eq] using htargetSpace
        have hcodeEq : codeVal = targetCode :=
          reverseBits_injective_of_lt hcodeValPow htargetPow hrevEq
        omega
      have hrowPres : row'[codeIdx]! = row[codeIdx]! := by
        simpa [row'] using
          getElem!_set!_ne row rev codeIdx (some i)
            (by simpa [row] using hcodeIdxBound) hne
      calc
        out[codeLen]![codeIdx]! = table'[codeLen]![codeIdx]! := hrec
        _ = row'[codeIdx]! := by rw [hrowSet]
        _ = row[codeIdx]! := hrowPres
        _ = table[codeLen]![codeIdx]! := by rfl
    · have hshape' :
        ∀ j (hj : j < lengths.size), i + 1 ≤ j →
          0 < lengths[j] → lengths[j] = codeLen := by
        intro j hj hle hposj
        exact hshape j hj (by omega) hposj
      have hbudget' :
          nextCode[codeLen]! + (lengths.size - (i + 1)) ≤ 1 <<< codeLen := by
        omega
      have hrec :=
        fillHuffmanTableAux_uniform_entry_eq_of_code_lt_next
          lengths (i + 1) codeLen nextCode table out targetCode codeIdx
          hshape' hnextIdx htableIdx hrow hbudget' htargetLt hcodeIdx
          (by simpa [hi, hpos] using hfill)
      exact hrec
  · have hout : table = out := by
      simpa [hi] using hfill
    rw [← hout]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Uniform Huffman table filling agrees with canonical reversed-code filling
at any positive target symbol. This is the row-nine lookup core for generated
literal/length payload decoding. -/
lemma fillHuffmanTableAux_uniform_lookup_of_canonical_at
    (lengths : Array Nat) (i codeLen : Nat) (nextCode : Array Nat)
    (table out : Array (Array (Option Nat)))
    (revCodes : Array (Nat × Nat)) (target : Nat)
    (hshape :
      ∀ j (hj : j < lengths.size), i ≤ j →
        0 < lengths[j] → lengths[j] = codeLen)
    (hnextIdx : codeLen < nextCode.size)
    (htableIdx : codeLen < table.size)
    (hrow : table[codeLen]!.size = 1 <<< codeLen)
    (hbudget : nextCode[codeLen]! + (lengths.size - i) ≤ 1 <<< codeLen)
    (htarget : target < lengths.size)
    (hle : i ≤ target)
    (hrevSize : revCodes.size = lengths.size)
    (hposTarget : 0 < lengths[target])
    (hfill :
      Png.fillHuffmanTableAux lengths i nextCode table = some out) :
    let codesOut := Png.fillCanonicalRevCodesAux lengths i nextCode revCodes
    out[codeLen]![codesOut[target]!.1]! = some target := by
  rw [Png.fillHuffmanTableAux.eq_1] at hfill
  have hi : i < lengths.size := lt_of_le_of_lt hle htarget
  by_cases hpos : 0 < lengths[i]
  · have hlen : lengths[i] = codeLen := hshape i hi le_rfl hpos
    have hcodeLenPos : 0 < codeLen := by
      simpa [hlen] using hpos
    let codeVal := nextCode[codeLen]!
    have hcodeValLt : codeVal < 1 <<< codeLen := by
      have hremainingPos : 0 < lengths.size - i := by omega
      dsimp [codeVal]
      omega
    have hnotCodeGe : ¬ codeVal >= (1 <<< codeLen) := by omega
    let nextCode' := nextCode.set! codeLen (codeVal + 1)
    let rev := Png.reverseBits codeVal codeLen
    let row := table[codeLen]!
    have hrevBound : rev < row.size := by
      rw [hrow]
      simpa [rev, row, Nat.shiftLeft_eq] using
        Png.reverseBits_lt codeVal codeLen
    have hnotRevGe : ¬ rev >= row.size := by omega
    let row' := row.set! rev (some i)
    let table' := table.set! codeLen row'
    let revCodes' := revCodes.set! i (rev, codeLen)
    have hfillRec :
        Png.fillHuffmanTableAux lengths (i + 1) nextCode' table' =
          some out := by
      simpa [hi, hpos, hlen, codeVal, hnotCodeGe, nextCode', rev, row,
        hnotRevGe, row', table', hcodeLenPos] using hfill
    have hnextIdx' : codeLen < nextCode'.size := by
      simp [nextCode', hnextIdx]
    have htableIdx' : codeLen < table'.size := by
      simp [table', htableIdx]
    have hnextAt :
        nextCode'[codeLen]! = codeVal + 1 := by
      simpa [nextCode'] using
        getElem!_set!_eq nextCode codeLen (codeVal + 1) hnextIdx
    have hrowSet : table'[codeLen]! = row' := by
      simpa [table'] using getElem!_set!_eq table codeLen row' htableIdx
    have hrow' : table'[codeLen]!.size = 1 <<< codeLen := by
      rw [hrowSet]
      simp [row', row, hrow]
    have hbudget' :
        nextCode'[codeLen]! + (lengths.size - (i + 1)) ≤ 1 <<< codeLen := by
      rw [hnextAt]
      omega
    have hshape' :
        ∀ j (hj : j < lengths.size), i + 1 ≤ j →
          0 < lengths[j] → lengths[j] = codeLen := by
      intro j hj hle' hposj
      exact hshape j hj (by omega) hposj
    have hcodesUnfold :
        Png.fillCanonicalRevCodesAux lengths i nextCode revCodes =
          Png.fillCanonicalRevCodesAux lengths (i + 1) nextCode' revCodes' := by
      rw [Png.fillCanonicalRevCodesAux.eq_1]
      simp [hi, hpos, hlen, codeVal, nextCode', rev, revCodes', hcodeLenPos]
    by_cases heq : i = target
    · subst target
      have htargetRev' : i < revCodes'.size := by
        simp [revCodes', hrevSize, hi]
      have hcodesPres :=
        fillCanonicalRevCodesAux_get!_of_lt lengths (i + 1) nextCode'
          revCodes' i htargetRev' (Nat.lt_succ_self i)
      have hsetRev : revCodes'[i]! = (rev, codeLen) := by
        have hiRev : i < revCodes.size := by
          simpa [hrevSize] using hi
        simpa [revCodes'] using
          getElem!_set!_eq revCodes i (rev, codeLen) hiRev
      have hcodesFst :
          (Png.fillCanonicalRevCodesAux lengths i nextCode revCodes)[i]!.1 =
            rev := by
        rw [hcodesUnfold]
        calc
          (Png.fillCanonicalRevCodesAux lengths (i + 1) nextCode'
              revCodes')[i]!.1 =
              revCodes'[i]!.1 := by
                simpa using congrArg Prod.fst hcodesPres
          _ = rev := by simp [hsetRev]
      have hentryTable' : table'[codeLen]![rev]! = some i := by
        rw [hrowSet]
        have hrowEntry : row'[rev]! = some i := by
          simpa [row'] using getElem!_set!_eq row rev (some i) hrevBound
        exact hrowEntry
      have hpres :=
        fillHuffmanTableAux_uniform_entry_eq_of_code_lt_next
          lengths (i + 1) codeLen nextCode' table' out codeVal rev
          hshape' hnextIdx' htableIdx' hrow' hbudget'
          (by rw [hnextAt]; omega) rfl hfillRec
      intro codesOut
      dsimp [codesOut]
      rw [hcodesFst]
      calc
        out[codeLen]![rev]! = table'[codeLen]![rev]! := hpres
        _ = some i := hentryTable'
    · have hltTarget : i < target := Nat.lt_of_le_of_ne hle heq
      have hrevSize' : revCodes'.size = lengths.size := by
        simp [revCodes', hrevSize]
      have hrec :=
        fillHuffmanTableAux_uniform_lookup_of_canonical_at
          lengths (i + 1) codeLen nextCode' table' out revCodes' target
          hshape' hnextIdx' htableIdx' hrow' hbudget' htarget
          (Nat.succ_le_of_lt hltTarget) hrevSize' hposTarget hfillRec
      intro codesOut
      dsimp [codesOut]
      rw [hcodesUnfold]
      exact hrec
  · have hshape' :
      ∀ j (hj : j < lengths.size), i + 1 ≤ j →
        0 < lengths[j] → lengths[j] = codeLen := by
      intro j hj hle' hposj
      exact hshape j hj (by omega) hposj
    have hbudget' :
        nextCode[codeLen]! + (lengths.size - (i + 1)) ≤ 1 <<< codeLen := by
      omega
    have hcodesUnfold :
        Png.fillCanonicalRevCodesAux lengths i nextCode revCodes =
          Png.fillCanonicalRevCodesAux lengths (i + 1) nextCode revCodes := by
      rw [Png.fillCanonicalRevCodesAux.eq_1]
      simp [hi, hpos]
    have hltTarget : i < target := by
      have hne : i ≠ target := by
        intro heq
        subst target
        exact hpos hposTarget
      exact Nat.lt_of_le_of_ne hle hne
    have hrec :=
      fillHuffmanTableAux_uniform_lookup_of_canonical_at
        lengths (i + 1) codeLen nextCode table out revCodes target
        hshape' hnextIdx htableIdx hrow hbudget' htarget
        (Nat.succ_le_of_lt hltTarget) hrevSize hposTarget
        (by simpa [hi, hpos] using hfill)
    intro codesOut
    dsimp [codesOut]
    rw [hcodesUnfold]
    exact hrec
termination_by target - i
decreasing_by
  all_goals
    have hlt : i < target := by omega
    exact Nat.sub_lt_sub_left (k := i) (m := target) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Names the generated literal/length Huffman table accepted by `mkHuffman`.
This lets the payload proof talk about the same table that the header parser
reconstructs, without unfolding the table builder at every use site. -/
def generatedDynamicLitLenTable (tokens : Array Png.DeflateToken) : Png.Huffman :=
  match Png.mkHuffman
    (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)) with
  | some table => table
  | none => Png.emptyHuffman

/-- Generated literal/length lengths build the named generated table. This
turns the existing `isSome` validity proof into an exact equation for payload
decode lemmas. -/
lemma mkHuffman_generatedDynamicLitLenLengths_eq
    (tokens : Array Png.DeflateToken) :
    Png.mkHuffman
      (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)) =
        some (generatedDynamicLitLenTable tokens) := by
  have hsome :=
    mkHuffman_generatedDynamicLitLenLengths_isSome tokens
  unfold generatedDynamicLitLenTable
  cases h :
      Png.mkHuffman
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)) with
  | none =>
      simp [h] at hsome
  | some table =>
      rfl

/-- The generated literal/length table has the uniform nine-bit maximum.
Payload decode proofs use this to unfold `Huffman.decode` with fixed fuel. -/
lemma generatedDynamicLitLenTable_maxLen
    (tokens : Array Png.DeflateToken) :
    (generatedDynamicLitLenTable tokens).maxLen = 9 := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode := (Png.nextCodesAux count 9 1 0 (Array.replicate 10 0)).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      simp [hfill] at hmk'
      rw [← hmk']

/-- The generated literal/length decode table has rows for lengths zero
through nine. Payload decode proofs use this for the final nine-bit row. -/
lemma generatedDynamicLitLenTable_table_size
    (tokens : Array Png.DeflateToken) :
    (generatedDynamicLitLenTable tokens).table.size = 10 := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode := (Png.nextCodesAux count 9 1 0 (Array.replicate 10 0)).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      have hsize :=
        fillHuffmanTableAux_size_of_some lengths 0 nextCode init table hfill
      simp [hfill] at hmk'
      rw [← hmk']
      calc
        table.size = init.size := hsize
        _ = 10 := by simp [init, huffmanEmptyTable_size]

/-- The generated literal/length table's nine-bit row has the expected 512
entries. This is the concrete row bound for generated payload symbol lookup. -/
lemma generatedDynamicLitLenTable_row9_size
    (tokens : Array Png.DeflateToken) :
    (generatedDynamicLitLenTable tokens).table[9]!.size = 512 := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode := (Png.nextCodesAux count 9 1 0 (Array.replicate 10 0)).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      have hrow : 9 < init.size := by
        simp [init, huffmanEmptyTable_size]
      have hsize :=
        fillHuffmanTableAux_row_size_of_some lengths 0 nextCode init table 9
          hrow hfill
      simp [hfill] at hmk'
      rw [← hmk']
      calc
        table[9]!.size = init[9]!.size := hsize
        _ = 512 := by
          have hinit := huffmanEmptyTable_get!_size 9 9 le_rfl (by decide)
          simpa [init, Nat.shiftLeft_eq] using hinit

/-- Generated literal/length rows shorter than nine bits are empty. This is
the continuation fact needed before a generated payload symbol resolves. -/
lemma generatedDynamicLitLenTable_short_row_get_none
    (tokens : Array Png.DeflateToken) (rowIdx code : Nat)
    (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 9)
    (hcode : code < (generatedDynamicLitLenTable tokens).table[rowIdx]!.size) :
    (generatedDynamicLitLenTable tokens).table[rowIdx]![code]! = none := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode := (Png.nextCodesAux count 9 1 0 (Array.replicate 10 0)).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      have hshape :
          ∀ j (hj : j < lengths.size), 0 ≤ j →
            0 < lengths[j] → lengths[j] = 9 := by
        intro j hj _hle hpos
        have hnine :
            lengths[j] = 9 := by
          simpa [lengths] using
            (generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine
              (Png.litLenSymbolFreqs tokens) j (by simpa [lengths] using hj)).mp
              (by simpa [lengths] using hpos)
        exact hnine
      have hrowInit : rowIdx < init.size := by
        simp [init, huffmanEmptyTable_size]
        omega
      have hrowNe : rowIdx ≠ 9 := by omega
      have hpres :=
        fillHuffmanTableAux_uniform_row_eq_of_ne lengths 0 9 nextCode init
          table rowIdx hshape hrowNe hrowInit hfill
      simp [hfill] at hmk'
      rw [← hmk'] at hcode ⊢
      have hcodeInit : code < init[rowIdx]!.size := by
        simpa [hpres] using hcode
      rw [hpres]
      have hinitRow :
          init[rowIdx]! =
            Array.replicate (1 <<< rowIdx) (none : Option Nat) := by
        rw [getElem!_pos init rowIdx hrowInit]
        simp [init, Png.huffmanEmptyTable, Nat.ne_of_gt hrowPos]
      rw [hinitRow]
      have hcodeRep :
          code < (Array.replicate (1 <<< rowIdx) (none : Option Nat)).size := by
        simpa [hinitRow] using hcodeInit
      rw [getElem!_pos
        (Array.replicate (1 <<< rowIdx) (none : Option Nat)) code hcodeRep]
      simp

/-- Generated literal/length rows below nine bits keep their initialized row
widths. This supplies the modulo bounds for short-prefix decoder steps. -/
lemma generatedDynamicLitLenTable_short_row_size
    (tokens : Array Png.DeflateToken) (rowIdx : Nat)
    (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 9) :
    (generatedDynamicLitLenTable tokens).table[rowIdx]!.size = 1 <<< rowIdx := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode := (Png.nextCodesAux count 9 1 0 (Array.replicate 10 0)).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      have hrowInit : rowIdx < init.size := by
        simp [init, huffmanEmptyTable_size]
        omega
      have hsize :=
        fillHuffmanTableAux_row_size_of_some lengths 0 nextCode init table rowIdx
          hrowInit hfill
      simp [hfill] at hmk'
      rw [← hmk']
      calc
        table[rowIdx]!.size = init[rowIdx]!.size := hsize
        _ = 1 <<< rowIdx := by
          exact huffmanEmptyTable_get!_size 9 rowIdx (by omega) hrowPos

/-- Any generated literal/length prefix shorter than nine bits is unresolved.
This is the packed-stream form used by the future `decodeFuel` proof. -/
lemma generatedDynamicLitLenTable_prefix_row_none
    (tokens : Array Png.DeflateToken) (bitsTot rowIdx : Nat)
    (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 9) :
    (generatedDynamicLitLenTable tokens).table[rowIdx]![bitsTot % 2 ^ rowIdx]! =
      none := by
  have hsize :=
    generatedDynamicLitLenTable_short_row_size tokens rowIdx hrowPos hrowLt
  have hcode :
      bitsTot % 2 ^ rowIdx <
        (generatedDynamicLitLenTable tokens).table[rowIdx]!.size := by
    have hpow : 0 < 2 ^ rowIdx := Nat.pow_pos (by decide : 0 < (2 : Nat))
    have hmod : bitsTot % 2 ^ rowIdx < 2 ^ rowIdx := Nat.mod_lt bitsTot hpow
    simpa [hsize, Nat.shiftLeft_eq] using hmod
  exact generatedDynamicLitLenTable_short_row_get_none tokens rowIdx
    (bitsTot % 2 ^ rowIdx) hrowPos hrowLt hcode

/-- The generated literal/length Huffman table maps every positive generated
canonical code back to its symbol. This is the payload-side table lookup core. -/
lemma generatedDynamicLitLenTable_lookup_generated_code_of_pos
    (tokens : Array Png.DeflateToken) (sym : Nat)
    (hsym :
      sym <
        (Png.generatedDynamicLitLenLengths
          (Png.litLenSymbolFreqs tokens)).size)
    (hpos :
      0 <
        (Png.generatedDynamicLitLenLengths
          (Png.litLenSymbolFreqs tokens))[sym]) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let codes := Png.canonicalRevCodesFromLengths lengths
    (generatedDynamicLitLenTable tokens).table[9]![codes[sym]!.1]! =
      some sym := by
  intro lengths codes
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode0 : Array Nat := Array.replicate 10 0
  let nextCode := (Png.nextCodesAux count 9 1 0 nextCode0).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode0, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      have hshape :
          ∀ j (hj : j < lengths.size), 0 ≤ j →
            0 < lengths[j] → lengths[j] = 9 := by
        intro j hj _hle hposj
        simpa [lengths] using
          (generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine
            (Png.litLenSymbolFreqs tokens) j (by simpa [lengths] using hj)).mp
            (by simpa [lengths] using hposj)
      have hnextSize : nextCode.size = nextCode0.size := by
        simpa [nextCode] using nextCodesAux_size count 9 1 0 nextCode0
      have hnextIdx : 9 < nextCode.size := by
        rw [hnextSize]
        simp [nextCode0]
      have htableIdx : 9 < init.size := by
        simp [init, huffmanEmptyTable_size]
      have hrow : init[9]!.size = 1 <<< 9 := by
        exact huffmanEmptyTable_get!_size 9 9 le_rfl (by decide)
      have hnextZero : nextCode[9]! = 0 := by
        have hscanned :=
          nextCodesAux_generatedDynamicLitLenLengths_get!_scannedMax_eq_zero tokens
        simpa [lengths, count, nextCode0, nextCode, hmax,
          Png.generatedDynamicLitLenCodeLen] using hscanned
      have hsizeLt : lengths.size < 1 <<< 9 := by
        have hlt := generatedDynamicLitLenLengths_size_lt_codeSpace tokens
        simpa [lengths, Png.generatedDynamicLitLenCodeLen, Nat.shiftLeft_eq] using hlt
      have hbudget : nextCode[9]! + (lengths.size - 0) ≤ 1 <<< 9 := by
        rw [hnextZero]
        omega
      have hlookup :=
        fillHuffmanTableAux_uniform_lookup_of_canonical_at
          lengths 0 9 nextCode init table (Array.replicate lengths.size (0, 0))
          sym hshape hnextIdx htableIdx hrow hbudget
          (by simpa [lengths] using hsym) (Nat.zero_le sym) (by simp)
          (by simpa [lengths] using hpos) hfill
      simp [hfill] at hmk'
      rw [← hmk']
      simpa [codes, Png.canonicalRevCodesFromLengths, lengths, count,
        nextCode0, nextCode, hmax, Png.generatedDynamicLitLenCodeLen] using hlookup

/-- Literal payload symbols resolve in the generated literal/length table.
This is the token-indexed lookup form for literal replay. -/
lemma generatedDynamicLitLenTable_lookup_literal_at
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let codes := Png.canonicalRevCodesFromLengths lengths
    (generatedDynamicLitLenTable tokens).table[9]![codes[b.toNat]!.1]! =
      some b.toNat := by
  intro lengths codes
  have hsym : b.toNat < lengths.size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]
    omega
  have hpos : 0 < lengths[b.toNat] := by
    have hposBang :=
      generatedDynamicLitLenLengths_literal_pos_at tokens target b htarget ht
    simpa [lengths, getElem!_pos lengths b.toNat hsym] using hposBang
  simpa [lengths, codes] using
    generatedDynamicLitLenTable_lookup_generated_code_of_pos
      tokens b.toNat (by simpa [lengths] using hsym) (by simpa [lengths] using hpos)

/-- Match payload literal/length symbols resolve in the generated table. This
is the token-indexed lookup form for distance-1 match replay. -/
lemma generatedDynamicLitLenTable_lookup_match_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let codes := Png.canonicalRevCodesFromLengths lengths
    let sym := (Png.fixedLenMatchInfo len).1
    (generatedDynamicLitLenTable tokens).table[9]![codes[sym]!.1]! =
      some sym := by
  intro lengths codes sym
  have hsym : sym < lengths.size := by
    have hfixed := fixedLenMatchInfo_sym_lt_286 len hlen
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]
    omega
  have hpos : 0 < lengths[sym] := by
    have hposBang :=
      generatedDynamicLitLenLengths_match_pos_at tokens target len htarget ht hlen
    simpa [lengths, sym, getElem!_pos lengths sym hsym] using hposBang
  simpa [lengths, codes, sym] using
    generatedDynamicLitLenTable_lookup_generated_code_of_pos
      tokens sym (by simpa [lengths] using hsym) (by simpa [lengths] using hpos)

/-- The generated end-of-block symbol resolves in the generated table. This is
the terminal lookup form for generated payload replay. -/
lemma generatedDynamicLitLenTable_lookup_eob
    (tokens : Array Png.DeflateToken) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let codes := Png.canonicalRevCodesFromLengths lengths
    (generatedDynamicLitLenTable tokens).table[9]![codes[256]!.1]! =
      some 256 := by
  intro lengths codes
  have hsym : 256 < lengths.size := by
    simpa [lengths] using generatedDynamicLitLenLengths_eob_inBounds tokens
  have hpos : 0 < lengths[256] := by
    simpa [lengths] using generatedDynamicLitLenLengths_eob_pos tokens
  simpa [lengths, codes] using
    generatedDynamicLitLenTable_lookup_generated_code_of_pos
      tokens 256 (by simpa [lengths] using hsym) (by simpa [lengths] using hpos)

/-- Appending later payload bits after a generated nine-bit literal/length code
preserves the row-nine lookup. This is the packed-stream final prefix lookup. -/
lemma generatedDynamicLitLenTable_prefix9_row_some
    (tokens : Array Png.DeflateToken) (sym restBits : Nat)
    (hsym :
      sym <
        (Png.generatedDynamicLitLenLengths
          (Png.litLenSymbolFreqs tokens)).size)
    (hpos :
      0 <
        (Png.generatedDynamicLitLenLengths
          (Png.litLenSymbolFreqs tokens))[sym]) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let codes := Png.canonicalRevCodesFromLengths lengths
    let bitsTot := codes[sym]!.1 ||| (restBits <<< 9)
    (generatedDynamicLitLenTable tokens).table[9]![bitsTot % 2 ^ 9]! =
      some sym := by
  intro lengths codes bitsTot
  have hlookup :=
    generatedDynamicLitLenTable_lookup_generated_code_of_pos
      tokens sym hsym hpos
  have hbits :
      codes[sym]!.1 < 2 ^ 9 := by
    have hposBang : 0 < lengths[sym]! := by
      simpa [getElem!_pos lengths sym (by simpa [lengths] using hsym)] using hpos
    have hraw :=
      generatedDynamicLitLenCodes_bits_lt_codeSpace_of_pos
        tokens sym hsym (by simpa [lengths] using hposBang)
    simpa [lengths, codes, Png.generatedDynamicLitLenCodeLen] using hraw
  have hmod :
      (codes[sym]!.1 ||| (restBits <<< 9)) % 2 ^ 9 =
        codes[sym]!.1 := by
    have h :=
      Png.mod_two_pow_or_shift
        (a := codes[sym]!.1) (b := restBits) (k := 9) (len := 9) le_rfl
    have hmodCode : codes[sym]!.1 % 2 ^ 9 = codes[sym]!.1 :=
      Nat.mod_eq_of_lt hbits
    simpa [hmodCode] using h
  simpa [lengths, codes, bitsTot, hmod] using hlookup

/-- Short generated literal/length prefixes fit in their internal decode rows.
This packages the row-size facts in the form expected by `decodeFuel`. -/
lemma generatedDynamicLitLenTable_prefix_code_lt_row_size
    (tokens : Array Png.DeflateToken) (bitsTot rowIdx : Nat)
    (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 9)
    (htable : rowIdx < (generatedDynamicLitLenTable tokens).table.size) :
    bitsTot % 2 ^ rowIdx <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table rowIdx htable).size := by
  have hrowGet :
      (generatedDynamicLitLenTable tokens).table[rowIdx]! =
        Array.getInternal (generatedDynamicLitLenTable tokens).table rowIdx htable := by
    rw [getElem!_pos (generatedDynamicLitLenTable tokens).table rowIdx htable]
    rfl
  have hsize :=
    generatedDynamicLitLenTable_short_row_size tokens rowIdx hrowPos hrowLt
  have hlt : bitsTot % 2 ^ rowIdx < 2 ^ rowIdx := by
    exact Nat.mod_lt bitsTot (Nat.pow_pos (by decide : 0 < (2 : Nat)))
  rw [← hrowGet]
  simpa [hsize, Nat.shiftLeft_eq] using hlt

/-- A generated literal/length nine-bit prefix fits in row nine. This is the
final-row bound needed before the successful decode step. -/
lemma generatedDynamicLitLenTable_prefix9_code_lt_row_size
    (tokens : Array Png.DeflateToken) (bitsTot : Nat)
    (htable : 9 < (generatedDynamicLitLenTable tokens).table.size) :
    bitsTot % 2 ^ 9 <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable).size := by
  have hrowGet :
      (generatedDynamicLitLenTable tokens).table[9]! =
        Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable := by
    rw [getElem!_pos (generatedDynamicLitLenTable tokens).table 9 htable]
    rfl
  have hlt : bitsTot % 2 ^ 9 < 512 := by
    simpa using Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 9)
  rw [← hrowGet]
  simpa [generatedDynamicLitLenTable_row9_size tokens] using hlt

/-- Internal-row form of unresolved generated literal/length prefixes. It lets
the generated payload proof feed row facts directly to `decodeFuel`. -/
lemma generatedDynamicLitLenTable_prefix_row_none_internal
    (tokens : Array Png.DeflateToken) (bitsTot rowIdx : Nat)
    (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 9)
    (htable : rowIdx < (generatedDynamicLitLenTable tokens).table.size)
    (hcode :
      bitsTot % 2 ^ rowIdx <
        (Array.getInternal (generatedDynamicLitLenTable tokens).table rowIdx htable).size) :
    Array.getInternal
      (Array.getInternal (generatedDynamicLitLenTable tokens).table rowIdx htable)
      (bitsTot % 2 ^ rowIdx) hcode = none := by
  have hrowGet :
      (generatedDynamicLitLenTable tokens).table[rowIdx]! =
        Array.getInternal (generatedDynamicLitLenTable tokens).table rowIdx htable := by
    rw [getElem!_pos (generatedDynamicLitLenTable tokens).table rowIdx htable]
    rfl
  have hentry :
      (generatedDynamicLitLenTable tokens).table[rowIdx]![bitsTot % 2 ^ rowIdx]! =
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table rowIdx htable)
          (bitsTot % 2 ^ rowIdx) hcode := by
    rw [hrowGet]
    rw [getElem!_pos
      (Array.getInternal (generatedDynamicLitLenTable tokens).table rowIdx htable)
      (bitsTot % 2 ^ rowIdx) hcode]
    rfl
  have hp :=
    generatedDynamicLitLenTable_prefix_row_none tokens bitsTot rowIdx hrowPos hrowLt
  rw [hentry] at hp
  exact hp

/-- Internal-row form of a successful generated literal/length nine-bit
lookup. This is the final row fact consumed by `decodeFuel`. -/
lemma generatedDynamicLitLenTable_prefix9_row_some_internal
    (tokens : Array Png.DeflateToken) (bitsTot sym : Nat)
    (hrow9 :
      (generatedDynamicLitLenTable tokens).table[9]![bitsTot % 2 ^ 9]! = some sym)
    (htable : 9 < (generatedDynamicLitLenTable tokens).table.size)
    (hcode :
      bitsTot % 2 ^ 9 <
        (Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable).size) :
    Array.getInternal
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable)
      (bitsTot % 2 ^ 9) hcode = some sym := by
  have hrowGet :
      (generatedDynamicLitLenTable tokens).table[9]! =
        Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable := by
    rw [getElem!_pos (generatedDynamicLitLenTable tokens).table 9 htable]
    rfl
  have hentry :
      (generatedDynamicLitLenTable tokens).table[9]![bitsTot % 2 ^ 9]! =
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable)
          (bitsTot % 2 ^ 9) hcode := by
    rw [hrowGet]
    rw [getElem!_pos
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable)
      (bitsTot % 2 ^ 9) hcode]
    rfl
  rw [hentry] at hrow9
  exact hrow9

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Decodes a generated nine-bit literal/length code from a writer-built
stream. This is the generic dynamic-Huffman bridge for payload replay. -/
lemma generatedDynamicLitLenTable_decode_readerAt_writeBits_core
    (tokens : Array Png.DeflateToken)
    (bw : Png.BitWriter) (bitsTot restLen sym : Nat)
    (hrow9 :
      (generatedDynamicLitLenTable tokens).table[9]![bitsTot % 2 ^ 9]! = some sym)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lenTot := 9 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br9 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 9) bw'.flush
      (by
        have hk : 9 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
    (generatedDynamicLitLenTable tokens).decode br0 = some (sym, br9) := by
  let lenTot := 9 + restLen
  let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
  let bw1 := Png.BitWriter.writeBits bw bitsTot 1
  let bw2 := Png.BitWriter.writeBits bw bitsTot 2
  let bw3 := Png.BitWriter.writeBits bw bitsTot 3
  let bw4 := Png.BitWriter.writeBits bw bitsTot 4
  let bw5 := Png.BitWriter.writeBits bw bitsTot 5
  let bw6 := Png.BitWriter.writeBits bw bitsTot 6
  let bw7 := Png.BitWriter.writeBits bw bitsTot 7
  let bw8 := Png.BitWriter.writeBits bw bitsTot 8
  let bw9 := Png.BitWriter.writeBits bw bitsTot 9
  let br0 := Png.BitWriter.readerAt bw bw'.flush
    (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br1 := Png.BitWriter.readerAt bw1 bw'.flush
    (by
      have hk : 1 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 1 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 1 hbit)
  let br2 := Png.BitWriter.readerAt bw2 bw'.flush
    (by
      have hk : 2 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 2 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 2 hbit)
  let br3 := Png.BitWriter.readerAt bw3 bw'.flush
    (by
      have hk : 3 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 3 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 3 hbit)
  let br4 := Png.BitWriter.readerAt bw4 bw'.flush
    (by
      have hk : 4 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 4 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 4 hbit)
  let br5 := Png.BitWriter.readerAt bw5 bw'.flush
    (by
      have hk : 5 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  let br6 := Png.BitWriter.readerAt bw6 bw'.flush
    (by
      have hk : 6 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 6 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 6 hbit)
  let br7 := Png.BitWriter.readerAt bw7 bw'.flush
    (by
      have hk : 7 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 7 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 7 hbit)
  let br8 := Png.BitWriter.readerAt bw8 bw'.flush
    (by
      have hk : 8 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 8 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 8 hbit)
  let br9 := Png.BitWriter.readerAt bw9 bw'.flush
    (by
      have hk : 9 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
  have hbit1 : bw1.bitPos < 8 := by
    simpa [bw1] using Png.bitPos_lt_8_writeBits bw bitsTot 1 hbit
  have hbit2 : bw2.bitPos < 8 := by
    simpa [bw2] using Png.bitPos_lt_8_writeBits bw bitsTot 2 hbit
  have hbit3 : bw3.bitPos < 8 := by
    simpa [bw3] using Png.bitPos_lt_8_writeBits bw bitsTot 3 hbit
  have hbit4 : bw4.bitPos < 8 := by
    simpa [bw4] using Png.bitPos_lt_8_writeBits bw bitsTot 4 hbit
  have hbit5 : bw5.bitPos < 8 := by
    simpa [bw5] using Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit
  have hbit6 : bw6.bitPos < 8 := by
    simpa [bw6] using Png.bitPos_lt_8_writeBits bw bitsTot 6 hbit
  have hbit7 : bw7.bitPos < 8 := by
    simpa [bw7] using Png.bitPos_lt_8_writeBits bw bitsTot 7 hbit
  have hbit8 : bw8.bitPos < 8 := by
    simpa [bw8] using Png.bitPos_lt_8_writeBits bw bitsTot 8 hbit
  have hcur1 : bw1.curClearAbove := by
    simpa [bw1] using Png.curClearAbove_writeBits bw bitsTot 1 hbit hcur
  have hcur2 : bw2.curClearAbove := by
    simpa [bw2] using Png.curClearAbove_writeBits bw bitsTot 2 hbit hcur
  have hcur3 : bw3.curClearAbove := by
    simpa [bw3] using Png.curClearAbove_writeBits bw bitsTot 3 hbit hcur
  have hcur4 : bw4.curClearAbove := by
    simpa [bw4] using Png.curClearAbove_writeBits bw bitsTot 4 hbit hcur
  have hcur5 : bw5.curClearAbove := by
    simpa [bw5] using Png.curClearAbove_writeBits bw bitsTot 5 hbit hcur
  have hcur6 : bw6.curClearAbove := by
    simpa [bw6] using Png.curClearAbove_writeBits bw bitsTot 6 hbit hcur
  have hcur7 : bw7.curClearAbove := by
    simpa [bw7] using Png.curClearAbove_writeBits bw bitsTot 7 hbit hcur
  have hcur8 : bw8.curClearAbove := by
    simpa [bw8] using Png.curClearAbove_writeBits bw bitsTot 8 hbit hcur
  have hsplit1 : bw' = Png.BitWriter.writeBits bw1 (bitsTot >>> 1) (lenTot - 1) := by
    have hk : 1 + (lenTot - 1) = lenTot := by omega
    simpa [bw', bw1, hk] using
      (Png.writeBits_split bw bitsTot 1 (lenTot - 1))
  have hsplit2 : bw' = Png.BitWriter.writeBits bw2 (bitsTot >>> 2) (lenTot - 2) := by
    have hk : 2 + (lenTot - 2) = lenTot := by omega
    simpa [bw', bw2, hk] using
      (Png.writeBits_split bw bitsTot 2 (lenTot - 2))
  have hsplit3 : bw' = Png.BitWriter.writeBits bw3 (bitsTot >>> 3) (lenTot - 3) := by
    have hk : 3 + (lenTot - 3) = lenTot := by omega
    simpa [bw', bw3, hk] using
      (Png.writeBits_split bw bitsTot 3 (lenTot - 3))
  have hsplit4 : bw' = Png.BitWriter.writeBits bw4 (bitsTot >>> 4) (lenTot - 4) := by
    have hk : 4 + (lenTot - 4) = lenTot := by omega
    simpa [bw', bw4, hk] using
      (Png.writeBits_split bw bitsTot 4 (lenTot - 4))
  have hsplit5 : bw' = Png.BitWriter.writeBits bw5 (bitsTot >>> 5) (lenTot - 5) := by
    have hk : 5 + (lenTot - 5) = lenTot := by omega
    simpa [bw', bw5, hk] using
      (Png.writeBits_split bw bitsTot 5 (lenTot - 5))
  have hsplit6 : bw' = Png.BitWriter.writeBits bw6 (bitsTot >>> 6) (lenTot - 6) := by
    have hk : 6 + (lenTot - 6) = lenTot := by omega
    simpa [bw', bw6, hk] using
      (Png.writeBits_split bw bitsTot 6 (lenTot - 6))
  have hsplit7 : bw' = Png.BitWriter.writeBits bw7 (bitsTot >>> 7) (lenTot - 7) := by
    have hk : 7 + (lenTot - 7) = lenTot := by omega
    simpa [bw', bw7, hk] using
      (Png.writeBits_split bw bitsTot 7 (lenTot - 7))
  have hsplit8 : bw' = Png.BitWriter.writeBits bw8 (bitsTot >>> 8) (lenTot - 8) := by
    have hk : 8 + (lenTot - 8) = lenTot := by omega
    simpa [bw', bw8, hk] using
      (Png.writeBits_split bw bitsTot 8 (lenTot - 8))
  have hbound0 : br0.bitIndex + 1 ≤ br0.data.size * 8 := by
    simpa [br0, bw', lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot)
        (k := 1) (by omega) hbit)
  have hbound1 : br1.bitIndex + 1 ≤ br1.data.size * 8 := by
    simpa [br1, bw', hsplit1, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw1) (bits := bitsTot >>> 1)
        (len := lenTot - 1) (k := 1) (by omega) hbit1)
  have hbound2 : br2.bitIndex + 1 ≤ br2.data.size * 8 := by
    simpa [br2, bw', hsplit2, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw2) (bits := bitsTot >>> 2)
        (len := lenTot - 2) (k := 1) (by omega) hbit2)
  have hbound3 : br3.bitIndex + 1 ≤ br3.data.size * 8 := by
    simpa [br3, bw', hsplit3, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw3) (bits := bitsTot >>> 3)
        (len := lenTot - 3) (k := 1) (by omega) hbit3)
  have hbound4 : br4.bitIndex + 1 ≤ br4.data.size * 8 := by
    simpa [br4, bw', hsplit4, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw4) (bits := bitsTot >>> 4)
        (len := lenTot - 4) (k := 1) (by omega) hbit4)
  have hbound5 : br5.bitIndex + 1 ≤ br5.data.size * 8 := by
    simpa [br5, bw', hsplit5, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw5) (bits := bitsTot >>> 5)
        (len := lenTot - 5) (k := 1) (by omega) hbit5)
  have hbound6 : br6.bitIndex + 1 ≤ br6.data.size * 8 := by
    simpa [br6, bw', hsplit6, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw6) (bits := bitsTot >>> 6)
        (len := lenTot - 6) (k := 1) (by omega) hbit6)
  have hbound7 : br7.bitIndex + 1 ≤ br7.data.size * 8 := by
    simpa [br7, bw', hsplit7, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw7) (bits := bitsTot >>> 7)
        (len := lenTot - 7) (k := 1) (by omega) hbit7)
  have hbound8 : br8.bitIndex + 1 ≤ br8.data.size * 8 := by
    simpa [br8, bw', hsplit8, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw8) (bits := bitsTot >>> 8)
        (len := lenTot - 8) (k := 1) (by omega) hbit8)
  have hread0 : br0.readBit = (bitsTot % 2, br1) := by
    simpa [br0, br1, bw', lenTot] using
      (Png.readBit_readerAt_writeBits (bw := bw) (bits := bitsTot)
        (len := lenTot) hbit hcur (by omega))
  have hbw2 : Png.BitWriter.writeBit bw1 ((bitsTot >>> 1) % 2) = bw2 := by
    simp [bw1, bw2, Png.BitWriter.writeBits]
  have hread1 : br1.readBit = ((bitsTot >>> 1) % 2, br2) := by
    simpa [br1, br2, bw', hsplit1, hbw2, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw1) (bits := bitsTot >>> 1) (len := lenTot - 1)
        hbit1 hcur1 (by omega))
  have hshift2 : bitsTot >>> 1 >>> 1 = bitsTot >>> 2 := by
    simpa using (Nat.shiftRight_add bitsTot 1 1)
  have hbw3 : Png.BitWriter.writeBit bw2 ((bitsTot >>> 2) % 2) = bw3 := by
    simp [bw2, bw3, Png.BitWriter.writeBits, hshift2]
  have hread2 : br2.readBit = ((bitsTot >>> 2) % 2, br3) := by
    simpa [br2, br3, bw', hsplit2, hbw3, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw2) (bits := bitsTot >>> 2) (len := lenTot - 2)
        hbit2 hcur2 (by omega))
  have hshift3 : bitsTot >>> 1 >>> 1 >>> 1 = bitsTot >>> 3 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 = bitsTot >>> 2 >>> 1 := by simp [hshift2]
      _ = bitsTot >>> 3 := by simpa using (Nat.shiftRight_add bitsTot 2 1)
  have hbw4 : Png.BitWriter.writeBit bw3 ((bitsTot >>> 3) % 2) = bw4 := by
    simp [bw3, bw4, Png.BitWriter.writeBits, hshift3]
  have hread3 : br3.readBit = ((bitsTot >>> 3) % 2, br4) := by
    simpa [br3, br4, bw', hsplit3, hbw4, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw3) (bits := bitsTot >>> 3) (len := lenTot - 3)
        hbit3 hcur3 (by omega))
  have hshift4 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 4 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 3 >>> 1 := by simp [hshift3]
      _ = bitsTot >>> 4 := by simpa using (Nat.shiftRight_add bitsTot 3 1)
  have hbw5 : Png.BitWriter.writeBit bw4 ((bitsTot >>> 4) % 2) = bw5 := by
    simp [bw4, bw5, Png.BitWriter.writeBits, hshift4]
  have hread4 : br4.readBit = ((bitsTot >>> 4) % 2, br5) := by
    simpa [br4, br5, bw', hsplit4, hbw5, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw4) (bits := bitsTot >>> 4) (len := lenTot - 4)
        hbit4 hcur4 (by omega))
  have hshift5 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 5 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 4 >>> 1 := by
        simp [hshift4]
      _ = bitsTot >>> 5 := by simpa using (Nat.shiftRight_add bitsTot 4 1)
  have hbw6 : Png.BitWriter.writeBit bw5 ((bitsTot >>> 5) % 2) = bw6 := by
    simp [bw5, bw6, Png.BitWriter.writeBits, hshift5]
  have hread5 : br5.readBit = ((bitsTot >>> 5) % 2, br6) := by
    simpa [br5, br6, bw', hsplit5, hbw6, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw5) (bits := bitsTot >>> 5) (len := lenTot - 5)
        hbit5 hcur5 (by omega))
  have hshift6 :
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 6 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 5 >>> 1 := by
        simp [hshift5]
      _ = bitsTot >>> 6 := by simpa using (Nat.shiftRight_add bitsTot 5 1)
  have hbw7 : Png.BitWriter.writeBit bw6 ((bitsTot >>> 6) % 2) = bw7 := by
    simp [bw6, bw7, Png.BitWriter.writeBits, hshift6]
  have hread6 : br6.readBit = ((bitsTot >>> 6) % 2, br7) := by
    simpa [br6, br7, bw', hsplit6, hbw7, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw6) (bits := bitsTot >>> 6) (len := lenTot - 6)
        hbit6 hcur6 (by omega))
  have hshift7 :
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 7 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 =
          bitsTot >>> 6 >>> 1 := by
        simp [hshift6]
      _ = bitsTot >>> 7 := by simpa using (Nat.shiftRight_add bitsTot 6 1)
  have hbw8 : Png.BitWriter.writeBit bw7 ((bitsTot >>> 7) % 2) = bw8 := by
    simp [bw7, bw8, Png.BitWriter.writeBits, hshift7]
  have hread7 : br7.readBit = ((bitsTot >>> 7) % 2, br8) := by
    simpa [br7, br8, bw', hsplit7, hbw8, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw7) (bits := bitsTot >>> 7) (len := lenTot - 7)
        hbit7 hcur7 (by omega))
  have hshift8 :
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 =
        bitsTot >>> 8 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 =
          bitsTot >>> 7 >>> 1 := by
        simp [hshift7]
      _ = bitsTot >>> 8 := by simpa using (Nat.shiftRight_add bitsTot 7 1)
  have hbw9 : Png.BitWriter.writeBit bw8 ((bitsTot >>> 8) % 2) = bw9 := by
    simp [bw8, bw9, Png.BitWriter.writeBits, hshift8]
  have hread8 : br8.readBit = ((bitsTot >>> 8) % 2, br9) := by
    simpa [br8, br9, bw', hsplit8, hbw9, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw8) (bits := bitsTot >>> 8) (len := lenTot - 8)
        hbit8 hcur8 (by omega))
  have hprefix2 :
      bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1) = bitsTot % 2 ^ 2 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 1).symm
  have hprefix3 :
      bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2) = bitsTot % 2 ^ 3 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 2).symm
  have hprefix4 :
      bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3) = bitsTot % 2 ^ 4 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 3).symm
  have hprefix5 :
      bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4) = bitsTot % 2 ^ 5 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 4).symm
  have hprefix6 :
      bitsTot % 2 ^ 5 ||| (((bitsTot >>> 5) % 2) <<< 5) = bitsTot % 2 ^ 6 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 5).symm
  have hprefix7 :
      bitsTot % 2 ^ 6 ||| (((bitsTot >>> 6) % 2) <<< 6) = bitsTot % 2 ^ 7 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 6).symm
  have hprefix8 :
      bitsTot % 2 ^ 7 ||| (((bitsTot >>> 7) % 2) <<< 7) = bitsTot % 2 ^ 8 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 7).symm
  have hprefix9 :
      bitsTot % 2 ^ 8 ||| (((bitsTot >>> 8) % 2) <<< 8) = bitsTot % 2 ^ 9 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 8).symm
  have htable1 : 1 < (generatedDynamicLitLenTable tokens).table.size := by
    rw [generatedDynamicLitLenTable_table_size]
    decide
  have htable2 : 2 < (generatedDynamicLitLenTable tokens).table.size := by
    rw [generatedDynamicLitLenTable_table_size]
    decide
  have htable3 : 3 < (generatedDynamicLitLenTable tokens).table.size := by
    rw [generatedDynamicLitLenTable_table_size]
    decide
  have htable4 : 4 < (generatedDynamicLitLenTable tokens).table.size := by
    rw [generatedDynamicLitLenTable_table_size]
    decide
  have htable5 : 5 < (generatedDynamicLitLenTable tokens).table.size := by
    rw [generatedDynamicLitLenTable_table_size]
    decide
  have htable6 : 6 < (generatedDynamicLitLenTable tokens).table.size := by
    rw [generatedDynamicLitLenTable_table_size]
    decide
  have htable7 : 7 < (generatedDynamicLitLenTable tokens).table.size := by
    rw [generatedDynamicLitLenTable_table_size]
    decide
  have htable8 : 8 < (generatedDynamicLitLenTable tokens).table.size := by
    rw [generatedDynamicLitLenTable_table_size]
    decide
  have htable9 : 9 < (generatedDynamicLitLenTable tokens).table.size := by
    rw [generatedDynamicLitLenTable_table_size]
    decide
  have hcode1 : bitsTot % 2 <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 1 htable1).size :=
    generatedDynamicLitLenTable_prefix_code_lt_row_size tokens bitsTot 1
      (by decide) (by decide) htable1
  have hcode2 : bitsTot % 2 ^ 2 <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 2 htable2).size :=
    generatedDynamicLitLenTable_prefix_code_lt_row_size tokens bitsTot 2
      (by decide) (by decide) htable2
  have hcode3 : bitsTot % 2 ^ 3 <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 3 htable3).size :=
    generatedDynamicLitLenTable_prefix_code_lt_row_size tokens bitsTot 3
      (by decide) (by decide) htable3
  have hcode4 : bitsTot % 2 ^ 4 <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 4 htable4).size :=
    generatedDynamicLitLenTable_prefix_code_lt_row_size tokens bitsTot 4
      (by decide) (by decide) htable4
  have hcode5 : bitsTot % 2 ^ 5 <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 5 htable5).size :=
    generatedDynamicLitLenTable_prefix_code_lt_row_size tokens bitsTot 5
      (by decide) (by decide) htable5
  have hcode6 : bitsTot % 2 ^ 6 <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 6 htable6).size :=
    generatedDynamicLitLenTable_prefix_code_lt_row_size tokens bitsTot 6
      (by decide) (by decide) htable6
  have hcode7 : bitsTot % 2 ^ 7 <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 7 htable7).size :=
    generatedDynamicLitLenTable_prefix_code_lt_row_size tokens bitsTot 7
      (by decide) (by decide) htable7
  have hcode8 : bitsTot % 2 ^ 8 <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 8 htable8).size :=
    generatedDynamicLitLenTable_prefix_code_lt_row_size tokens bitsTot 8
      (by decide) (by decide) htable8
  have hcode9 : bitsTot % 2 ^ 9 <
      (Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable9).size :=
    generatedDynamicLitLenTable_prefix9_code_lt_row_size tokens bitsTot htable9
  have hrow1 :
      Array.getInternal (Array.getInternal (generatedDynamicLitLenTable tokens).table 1 htable1)
        (bitsTot % 2) hcode1 = none :=
    generatedDynamicLitLenTable_prefix_row_none_internal tokens bitsTot 1
      (by decide) (by decide) htable1 hcode1
  have hrow2 :
      Array.getInternal (Array.getInternal (generatedDynamicLitLenTable tokens).table 2 htable2)
        (bitsTot % 2 ^ 2) hcode2 = none :=
    generatedDynamicLitLenTable_prefix_row_none_internal tokens bitsTot 2
      (by decide) (by decide) htable2 hcode2
  have hrow3 :
      Array.getInternal (Array.getInternal (generatedDynamicLitLenTable tokens).table 3 htable3)
        (bitsTot % 2 ^ 3) hcode3 = none :=
    generatedDynamicLitLenTable_prefix_row_none_internal tokens bitsTot 3
      (by decide) (by decide) htable3 hcode3
  have hrow4 :
      Array.getInternal (Array.getInternal (generatedDynamicLitLenTable tokens).table 4 htable4)
        (bitsTot % 2 ^ 4) hcode4 = none :=
    generatedDynamicLitLenTable_prefix_row_none_internal tokens bitsTot 4
      (by decide) (by decide) htable4 hcode4
  have hrow5 :
      Array.getInternal (Array.getInternal (generatedDynamicLitLenTable tokens).table 5 htable5)
        (bitsTot % 2 ^ 5) hcode5 = none :=
    generatedDynamicLitLenTable_prefix_row_none_internal tokens bitsTot 5
      (by decide) (by decide) htable5 hcode5
  have hrow6 :
      Array.getInternal (Array.getInternal (generatedDynamicLitLenTable tokens).table 6 htable6)
        (bitsTot % 2 ^ 6) hcode6 = none :=
    generatedDynamicLitLenTable_prefix_row_none_internal tokens bitsTot 6
      (by decide) (by decide) htable6 hcode6
  have hrow7 :
      Array.getInternal (Array.getInternal (generatedDynamicLitLenTable tokens).table 7 htable7)
        (bitsTot % 2 ^ 7) hcode7 = none :=
    generatedDynamicLitLenTable_prefix_row_none_internal tokens bitsTot 7
      (by decide) (by decide) htable7 hcode7
  have hrow8 :
      Array.getInternal (Array.getInternal (generatedDynamicLitLenTable tokens).table 8 htable8)
        (bitsTot % 2 ^ 8) hcode8 = none :=
    generatedDynamicLitLenTable_prefix_row_none_internal tokens bitsTot 8
      (by decide) (by decide) htable8 hcode8
  have hrow9' :
      Array.getInternal (Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable9)
        (bitsTot % 2 ^ 9) hcode9 = some sym :=
    generatedDynamicLitLenTable_prefix9_row_some_internal
      tokens bitsTot sym hrow9 htable9 hcode9
  have hbr0 : br0.bytePos < br0.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br0 (by omega)
  have hbr7 : br7.bytePos < br7.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br7 (by omega)
  have hbr8 : br8.bytePos < br8.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br8 (by omega)
  have hstep0 :
      (generatedDynamicLitLenTable tokens).decode br0 =
        Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 8 (bitsTot % 2) 1 br1 := by
    have hcode1' :
        0 ||| ((bitsTot % 2) <<< 0) <
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 1 htable1).size := by
      simpa using hcode1
    have hrow1' :
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 1 htable1)
          (0 ||| ((bitsTot % 2) <<< 0)) hcode1' = none := by
      simpa using hrow1
    unfold Png.Huffman.decode
    rw [generatedDynamicLitLenTable_maxLen tokens]
    simpa [hread0] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicLitLenTable tokens)
        (fuel := 8) (code := 0) (len := 0) (br := br0) (br' := br1)
        (bit := bitsTot % 2) (hbyte := hbr0) (hread := hread0)
        (htable := htable1) (hcode := hcode1') (hrow := hrow1'))
  have hstep1 :
      Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 8 (bitsTot % 2) 1 br1 =
        Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 7 (bitsTot % 2 ^ 2) 2 br2 := by
    have hcode' :
        bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1) <
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 2 htable2).size := by
      simpa [hprefix2] using hcode2
    have hrow'' :
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 2 htable2)
          (bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1)) hcode' = none := by
      simpa [hprefix2] using hrow2
    simpa [hprefix2] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicLitLenTable tokens)
        (fuel := 7) (code := bitsTot % 2) (len := 1)
        (br := br1) (br' := br2) (bit := (bitsTot >>> 1) % 2)
        (hbyte := Png.bytePos_lt_of_bitIndex_lt_dataBits br1 (by omega))
        (hread := hread1) (htable := htable2) (hcode := hcode') (hrow := hrow''))
  have hstep2 :
      Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 7 (bitsTot % 2 ^ 2) 2 br2 =
        Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 6 (bitsTot % 2 ^ 3) 3 br3 := by
    have hcode' :
        bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2) <
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 3 htable3).size := by
      simpa [hprefix3] using hcode3
    have hrow'' :
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 3 htable3)
          (bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2)) hcode' = none := by
      simpa [hprefix3] using hrow3
    simpa [hprefix3] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicLitLenTable tokens)
        (fuel := 6) (code := bitsTot % 2 ^ 2) (len := 2)
        (br := br2) (br' := br3) (bit := (bitsTot >>> 2) % 2)
        (hbyte := Png.bytePos_lt_of_bitIndex_lt_dataBits br2 (by omega))
        (hread := hread2) (htable := htable3) (hcode := hcode') (hrow := hrow''))
  have hstep3 :
      Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 6 (bitsTot % 2 ^ 3) 3 br3 =
        Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 5 (bitsTot % 2 ^ 4) 4 br4 := by
    have hcode' :
        bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3) <
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 4 htable4).size := by
      simpa [hprefix4] using hcode4
    have hrow'' :
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 4 htable4)
          (bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3)) hcode' = none := by
      simpa [hprefix4] using hrow4
    simpa [hprefix4] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicLitLenTable tokens)
        (fuel := 5) (code := bitsTot % 2 ^ 3) (len := 3)
        (br := br3) (br' := br4) (bit := (bitsTot >>> 3) % 2)
        (hbyte := Png.bytePos_lt_of_bitIndex_lt_dataBits br3 (by omega))
        (hread := hread3) (htable := htable4) (hcode := hcode') (hrow := hrow''))
  have hstep4 :
      Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 5 (bitsTot % 2 ^ 4) 4 br4 =
        Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 4 (bitsTot % 2 ^ 5) 5 br5 := by
    have hcode' :
        bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4) <
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 5 htable5).size := by
      simpa [hprefix5] using hcode5
    have hrow'' :
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 5 htable5)
          (bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4)) hcode' = none := by
      simpa [hprefix5] using hrow5
    simpa [hprefix5] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicLitLenTable tokens)
        (fuel := 4) (code := bitsTot % 2 ^ 4) (len := 4)
        (br := br4) (br' := br5) (bit := (bitsTot >>> 4) % 2)
        (hbyte := Png.bytePos_lt_of_bitIndex_lt_dataBits br4 (by omega))
        (hread := hread4) (htable := htable5) (hcode := hcode') (hrow := hrow''))
  have hstep5 :
      Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 4 (bitsTot % 2 ^ 5) 5 br5 =
        Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 3 (bitsTot % 2 ^ 6) 6 br6 := by
    have hcode' :
        bitsTot % 2 ^ 5 ||| (((bitsTot >>> 5) % 2) <<< 5) <
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 6 htable6).size := by
      simpa [hprefix6] using hcode6
    have hrow'' :
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 6 htable6)
          (bitsTot % 2 ^ 5 ||| (((bitsTot >>> 5) % 2) <<< 5)) hcode' = none := by
      simpa [hprefix6] using hrow6
    simpa [hprefix6] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicLitLenTable tokens)
        (fuel := 3) (code := bitsTot % 2 ^ 5) (len := 5)
        (br := br5) (br' := br6) (bit := (bitsTot >>> 5) % 2)
        (hbyte := Png.bytePos_lt_of_bitIndex_lt_dataBits br5 (by omega))
        (hread := hread5) (htable := htable6) (hcode := hcode') (hrow := hrow''))
  have hstep6 :
      Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 3 (bitsTot % 2 ^ 6) 6 br6 =
        Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 2 (bitsTot % 2 ^ 7) 7 br7 := by
    have hcode' :
        bitsTot % 2 ^ 6 ||| (((bitsTot >>> 6) % 2) <<< 6) <
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 7 htable7).size := by
      simpa [hprefix7] using hcode7
    have hrow'' :
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 7 htable7)
          (bitsTot % 2 ^ 6 ||| (((bitsTot >>> 6) % 2) <<< 6)) hcode' = none := by
      simpa [hprefix7] using hrow7
    simpa [hprefix7] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicLitLenTable tokens)
        (fuel := 2) (code := bitsTot % 2 ^ 6) (len := 6)
        (br := br6) (br' := br7) (bit := (bitsTot >>> 6) % 2)
        (hbyte := Png.bytePos_lt_of_bitIndex_lt_dataBits br6 (by omega))
        (hread := hread6) (htable := htable7) (hcode := hcode') (hrow := hrow''))
  have hstep7 :
      Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 2 (bitsTot % 2 ^ 7) 7 br7 =
        Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 1 (bitsTot % 2 ^ 8) 8 br8 := by
    have hcode' :
        bitsTot % 2 ^ 7 ||| (((bitsTot >>> 7) % 2) <<< 7) <
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 8 htable8).size := by
      simpa [hprefix8] using hcode8
    have hrow'' :
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 8 htable8)
          (bitsTot % 2 ^ 7 ||| (((bitsTot >>> 7) % 2) <<< 7)) hcode' = none := by
      simpa [hprefix8] using hrow8
    simpa [hprefix8] using
      (Png.Huffman.decodeFuel_step_none (h := generatedDynamicLitLenTable tokens)
        (fuel := 1) (code := bitsTot % 2 ^ 7) (len := 7)
        (br := br7) (br' := br8) (bit := (bitsTot >>> 7) % 2)
        (hbyte := hbr7) (hread := hread7) (htable := htable8)
        (hcode := hcode') (hrow := hrow''))
  have hstep8 :
      Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 1
          (bitsTot % 2 ^ 8) 8 br8 =
        some (sym, br9) := by
    have hcode' :
        bitsTot % 2 ^ 8 ||| (((bitsTot >>> 8) % 2) <<< 8) <
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable9).size := by
      simpa [hprefix9] using hcode9
    have hrow'' :
        Array.getInternal
          (Array.getInternal (generatedDynamicLitLenTable tokens).table 9 htable9)
          (bitsTot % 2 ^ 8 ||| (((bitsTot >>> 8) % 2) <<< 8)) hcode' = some sym := by
      simpa [hprefix9] using hrow9'
    simpa [hprefix9] using
      (Png.Huffman.decodeFuel_step_some (h := generatedDynamicLitLenTable tokens)
        (fuel := 0) (code := bitsTot % 2 ^ 8) (len := 8)
        (br := br8) (br' := br9) (bit := (bitsTot >>> 8) % 2)
        (sym := sym) (hbyte := hbr8) (hread := hread8)
        (htable := htable9) (hcode := hcode') (hrow := hrow''))
  calc
    (generatedDynamicLitLenTable tokens).decode br0 =
        Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 8
          (bitsTot % 2) 1 br1 := hstep0
    _ = Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 7
          (bitsTot % 2 ^ 2) 2 br2 := hstep1
    _ = Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 6
          (bitsTot % 2 ^ 3) 3 br3 := hstep2
    _ = Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 5
          (bitsTot % 2 ^ 4) 4 br4 := hstep3
    _ = Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 4
          (bitsTot % 2 ^ 5) 5 br5 := hstep4
    _ = Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 3
          (bitsTot % 2 ^ 6) 6 br6 := hstep5
    _ = Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 2
          (bitsTot % 2 ^ 7) 7 br7 := hstep6
    _ = Png.Huffman.decodeFuel (generatedDynamicLitLenTable tokens) 1
          (bitsTot % 2 ^ 8) 8 br8 := hstep7
    _ = some (sym, br9) := hstep8

/-- A generated literal token's literal/length code decodes to the literal
symbol from the same writer-built payload stream. -/
lemma generatedDynamicLitLenTable_decode_literal_at_readerAt_writeBits
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (bw : Png.BitWriter) (restBits restLen : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let codes := Png.canonicalRevCodesFromLengths lengths
    let bitsTot := codes[b.toNat]!.1 ||| (restBits <<< 9)
    let lenTot := 9 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br9 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 9) bw'.flush
      (by
        have hk : 9 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
    (generatedDynamicLitLenTable tokens).decode br0 = some (b.toNat, br9) := by
  intro lengths codes bitsTot lenTot bw' br0 br9
  have hsym : b.toNat < lengths.size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]
    omega
  have hpos : 0 < lengths[b.toNat] := by
    have hposBang :=
      generatedDynamicLitLenLengths_literal_pos_at tokens target b htarget ht
    simpa [lengths, getElem!_pos lengths b.toNat hsym] using hposBang
  have hrow9 :
      (generatedDynamicLitLenTable tokens).table[9]![bitsTot % 2 ^ 9]! =
        some b.toNat := by
    simpa [lengths, codes, bitsTot] using
      (generatedDynamicLitLenTable_prefix9_row_some
        tokens b.toNat restBits
        (by simpa [lengths] using hsym)
        (by simpa [lengths] using hpos))
  simpa [bitsTot, lenTot, bw', br0, br9] using
    generatedDynamicLitLenTable_decode_readerAt_writeBits_core
      tokens bw bitsTot restLen b.toNat hrow9 hbit hcur

/-- A generated match token's literal/length code decodes to its DEFLATE
length symbol. Length extra bits are handled separately by payload replay. -/
lemma generatedDynamicLitLenTable_decode_match_at_readerAt_writeBits
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (bw : Png.BitWriter) (restBits restLen : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let codes := Png.canonicalRevCodesFromLengths lengths
    let sym := (Png.fixedLenMatchInfo len).1
    let bitsTot := codes[sym]!.1 ||| (restBits <<< 9)
    let lenTot := 9 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br9 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 9) bw'.flush
      (by
        have hk : 9 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
    (generatedDynamicLitLenTable tokens).decode br0 = some (sym, br9) := by
  intro lengths codes sym bitsTot lenTot bw' br0 br9
  have hsym : sym < lengths.size := by
    have hfixed := fixedLenMatchInfo_sym_lt_286 len hlen
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]
    omega
  have hpos : 0 < lengths[sym] := by
    have hposBang :=
      generatedDynamicLitLenLengths_match_pos_at tokens target len htarget ht hlen
    simpa [lengths, sym, getElem!_pos lengths sym hsym] using hposBang
  have hrow9 :
      (generatedDynamicLitLenTable tokens).table[9]![bitsTot % 2 ^ 9]! =
        some sym := by
    simpa [lengths, codes, sym, bitsTot] using
      (generatedDynamicLitLenTable_prefix9_row_some
        tokens sym restBits
        (by simpa [lengths] using hsym)
        (by simpa [lengths] using hpos))
  simpa [bitsTot, lenTot, bw', br0, br9] using
    generatedDynamicLitLenTable_decode_readerAt_writeBits_core
      tokens bw bitsTot restLen sym hrow9 hbit hcur

/-- The generated end-of-block code decodes through the generic dynamic
literal/length table. This supplies the terminal payload trace step. -/
lemma generatedDynamicLitLenTable_decode_eob_readerAt_writeBits
    (tokens : Array Png.DeflateToken)
    (bw : Png.BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let codes := Png.canonicalRevCodesFromLengths lengths
    let bitsTot := codes[256]!.1 ||| (restBits <<< 9)
    let lenTot := 9 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br9 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 9) bw'.flush
      (by
        have hk : 9 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
    (generatedDynamicLitLenTable tokens).decode br0 = some (256, br9) := by
  intro lengths codes bitsTot lenTot bw' br0 br9
  have hsym : 256 < lengths.size := by
    simpa [lengths] using generatedDynamicLitLenLengths_eob_inBounds tokens
  have hpos : 0 < lengths[256] := by
    simpa [lengths] using generatedDynamicLitLenLengths_eob_pos tokens
  have hrow9 :
      (generatedDynamicLitLenTable tokens).table[9]![bitsTot % 2 ^ 9]! =
        some 256 := by
    simpa [lengths, codes, bitsTot] using
      (generatedDynamicLitLenTable_prefix9_row_some
        tokens 256 restBits
        (by simpa [lengths] using hsym)
        (by simpa [lengths] using hpos))
  simpa [bitsTot, lenTot, bw', br0, br9] using
    generatedDynamicLitLenTable_decode_readerAt_writeBits_core
      tokens bw bitsTot restLen 256 hrow9 hbit hcur

/-- Names the generated dynamic distance table accepted by the parser boundary.
The table is empty for literal-only generated streams and non-empty when
distance-1 match tokens are present. -/
def generatedDynamicDistTable (tokens : Array Png.DeflateToken) : Png.Huffman :=
  match Png.buildDynamicDistTable
    (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)) with
  | some table => table
  | none => Png.emptyHuffman

/-- Generated distance lengths build the named generated distance table. This
packages both the match-bearing and literal-only dynamic-block cases. -/
lemma buildDynamicDistTable_generatedDynamicDistLengths_eq
    (tokens : Array Png.DeflateToken) :
    Png.buildDynamicDistTable
      (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)) =
        some (generatedDynamicDistTable tokens) := by
  obtain ⟨distTable, hdist⟩ :=
    buildDynamicDistTable_generatedDynamicDistLengths_exists tokens
  unfold generatedDynamicDistTable
  rw [hdist]

/-- Names the concrete generated distance table used whenever a distance-1
match token is present. The generated distance table then has only symbol zero. -/
def generatedDynamicDistMatchTable : Png.Huffman :=
  match Png.buildDynamicDistTable
    (Array.ofFn (fun idx : Fin 30 => if idx.val == 0 then 1 else 0)) with
  | some table => table
  | none => Png.emptyHuffman

/-- The concrete match-bearing generated distance shape builds the named table.
This turns the shape theorem into a stable table for payload replay. -/
lemma buildDynamicDistTable_generatedDistMatchShape_eq :
    Png.buildDynamicDistTable
      (Array.ofFn (fun idx : Fin 30 => if idx.val == 0 then 1 else 0)) =
        some generatedDynamicDistMatchTable := by
  native_decide

/-- A generated distance table with a match token is exactly the concrete
single-symbol distance-zero table. -/
lemma generatedDynamicDistTable_eq_matchTable_of_match_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len) :
    generatedDynamicDistTable tokens = generatedDynamicDistMatchTable := by
  let freqs := Png.distSymbolFreqs tokens
  have hfreq : 0 < freqs[0]! := by
    have hmatch := deflateTokensHasMatchDist1_true_of_match_at
      tokens target len htarget ht
    simpa [freqs] using distSymbolFreqs_zero_pos_of_hasMatch tokens hmatch
  have hshape :
      Png.generatedDynamicDistLengths freqs =
        Array.ofFn (fun idx : Fin 30 => if idx.val == 0 then 1 else 0) :=
    generatedDynamicDistLengths_eq_matchShape freqs
      (by simpa [freqs] using distSymbolFreqs_size tokens) hfreq
  unfold generatedDynamicDistTable
  rw [hshape, buildDynamicDistTable_generatedDistMatchShape_eq]

/-- The match-bearing generated distance table has one-bit codes. This is the
distance-side fuel fact for match payload decoding. -/
lemma generatedDynamicDistMatchTable_maxLen :
    generatedDynamicDistMatchTable.maxLen = 1 := by
  native_decide

/-- The match-bearing generated distance table has rows zero and one. -/
lemma generatedDynamicDistMatchTable_table_size :
    generatedDynamicDistMatchTable.table.size = 2 := by
  native_decide

/-- The one-bit generated distance row has two entries. -/
lemma generatedDynamicDistMatchTable_row1_size :
    generatedDynamicDistMatchTable.table[1]!.size = 2 := by
  native_decide

/-- The generated distance code for symbol zero is the one-bit zero code in
the match-bearing distance table. -/
lemma generatedDynamicDistMatchCodes_zero :
    (Png.canonicalRevCodesFromLengths
      (Array.ofFn (fun idx : Fin 30 => if idx.val == 0 then 1 else 0)))[0]! =
        (0, 1) := by
  native_decide

/-- Match-bearing generated distance code lookup for symbol zero is exactly
the one-bit zero code. This connects the runtime distance writer to distance-1
payload replay. -/
lemma generatedDynamicDistCodes_zero_eq_of_match_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len) :
    let lengths :=
      Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
    let codes := Png.canonicalRevCodesFromLengths lengths
    codes[0]! = (0, 1) := by
  intro lengths codes
  let freqs := Png.distSymbolFreqs tokens
  have hfreq : 0 < freqs[0]! := by
    have hmatch := deflateTokensHasMatchDist1_true_of_match_at
      tokens target len htarget ht
    simpa [freqs] using distSymbolFreqs_zero_pos_of_hasMatch tokens hmatch
  have hshape :
      lengths =
        Array.ofFn (fun idx : Fin 30 => if idx.val == 0 then 1 else 0) := by
    simpa [lengths, freqs] using
      generatedDynamicDistLengths_eq_matchShape freqs
        (by simpa [freqs] using distSymbolFreqs_size tokens) hfreq
  simpa [codes, hshape] using generatedDynamicDistMatchCodes_zero

/-- The match-bearing generated distance table maps the generated zero code
back to distance symbol zero. -/
lemma generatedDynamicDistMatchTable_lookup_zero :
    generatedDynamicDistMatchTable.table[1]![0]! = some 0 := by
  native_decide

/-- Match tokens resolve distance symbol zero in the generated distance table.
This is the distance-side lookup core for generated payload replay. -/
lemma generatedDynamicDistTable_lookup_zero_of_match_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len) :
    let lengths :=
      Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
    let codes := Png.canonicalRevCodesFromLengths lengths
    (generatedDynamicDistTable tokens).table[codes[0]!.2]![codes[0]!.1]! =
      some 0 := by
  intro lengths codes
  let freqs := Png.distSymbolFreqs tokens
  have hfreq : 0 < freqs[0]! := by
    have hmatch := deflateTokensHasMatchDist1_true_of_match_at
      tokens target len htarget ht
    simpa [freqs] using distSymbolFreqs_zero_pos_of_hasMatch tokens hmatch
  have hshape :
      lengths =
        Array.ofFn (fun idx : Fin 30 => if idx.val == 0 then 1 else 0) := by
    simpa [lengths, freqs] using
      generatedDynamicDistLengths_eq_matchShape freqs
        (by simpa [freqs] using distSymbolFreqs_size tokens) hfreq
  have htable :=
    generatedDynamicDistTable_eq_matchTable_of_match_at
      tokens target len htarget ht
  rw [htable]
  change generatedDynamicDistMatchTable.table[
      (Png.canonicalRevCodesFromLengths lengths)[0]!.2]![
        (Png.canonicalRevCodesFromLengths lengths)[0]!.1]! = some 0
  rw [hshape]
  rw [generatedDynamicDistMatchCodes_zero]
  exact generatedDynamicDistMatchTable_lookup_zero

/-- Decodes the generated one-bit distance-zero symbol from a writer-built
stream. This is the distance-side Huffman bridge for match payload replay. -/
lemma generatedDynamicDistMatchTable_decode_zero_readerAt_writeBits
    (bw : Png.BitWriter) (bitsTot restLen : Nat)
    (hrow1 : generatedDynamicDistMatchTable.table[1]![bitsTot % 2]! = some 0)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lenTot := 1 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br1 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 1) bw'.flush
      (by
        have hk : 1 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 1 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 1 hbit)
    generatedDynamicDistMatchTable.decode br0 = some (0, br1) := by
  let lenTot := 1 + restLen
  let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
  let bw1 := Png.BitWriter.writeBits bw bitsTot 1
  let br0 := Png.BitWriter.readerAt bw bw'.flush
    (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br1 := Png.BitWriter.readerAt bw1 bw'.flush
    (by
      have hk : 1 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 1 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 1 hbit)
  have hbound0 : br0.bitIndex + 1 ≤ br0.data.size * 8 := by
    simpa [br0, bw', lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot)
        (k := 1) (by omega) hbit)
  have hbr0 : br0.bytePos < br0.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br0 (by omega)
  have hread0 : br0.readBit = (bitsTot % 2, br1) := by
    simpa [br0, br1, bw', bw1, lenTot] using
      (Png.readBit_readerAt_writeBits (bw := bw) (bits := bitsTot) (len := lenTot)
        hbit hcur (by omega))
  have htable1 : 1 < generatedDynamicDistMatchTable.table.size := by
    rw [generatedDynamicDistMatchTable_table_size]
    decide
  have hrowGet1 :
      generatedDynamicDistMatchTable.table[1]! =
        Array.getInternal generatedDynamicDistMatchTable.table 1 htable1 := by
    rw [getElem!_pos generatedDynamicDistMatchTable.table 1 htable1]
    rfl
  have hcode1 : bitsTot % 2 <
      (Array.getInternal generatedDynamicDistMatchTable.table 1 htable1).size := by
    have hlt : bitsTot % 2 < 2 := Nat.mod_lt bitsTot (by decide)
    rw [← hrowGet1]
    simpa [generatedDynamicDistMatchTable_row1_size] using hlt
  have hrow1' :
      Array.getInternal
        (Array.getInternal generatedDynamicDistMatchTable.table 1 htable1)
        (bitsTot % 2) hcode1 = some 0 := by
    have hentry :
        generatedDynamicDistMatchTable.table[1]![bitsTot % 2]! =
          Array.getInternal
            (Array.getInternal generatedDynamicDistMatchTable.table 1 htable1)
            (bitsTot % 2) hcode1 := by
      rw [hrowGet1]
      rw [getElem!_pos
        (Array.getInternal generatedDynamicDistMatchTable.table 1 htable1)
        (bitsTot % 2) hcode1]
      rfl
    rw [hentry] at hrow1
    exact hrow1
  have hcode1' :
      0 ||| ((bitsTot % 2) <<< 0) <
        (Array.getInternal generatedDynamicDistMatchTable.table 1 htable1).size := by
    simpa using hcode1
  have hrow1'' :
      Array.getInternal
        (Array.getInternal generatedDynamicDistMatchTable.table 1 htable1)
        (0 ||| ((bitsTot % 2) <<< 0)) hcode1' = some 0 := by
    simpa using hrow1'
  unfold Png.Huffman.decode
  rw [generatedDynamicDistMatchTable_maxLen]
  simpa [hread0] using
    (Png.Huffman.decodeFuel_step_some (h := generatedDynamicDistMatchTable)
      (fuel := 0) (code := 0) (len := 0) (br := br0) (br' := br1)
      (bit := bitsTot % 2) (sym := 0) (hbyte := hbr0)
      (hread := hread0) (htable := htable1) (hcode := hcode1')
      (hrow := hrow1''))

/-- A generated match token's distance code decodes to distance symbol zero
through the generated distance table, not a fixed-table shortcut. -/
lemma generatedDynamicDistTable_decode_zero_of_match_at_readerAt_writeBits
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (bw : Png.BitWriter) (restBits restLen : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := restBits <<< 1
    let lenTot := 1 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br1 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 1) bw'.flush
      (by
        have hk : 1 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 1 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 1 hbit)
    (generatedDynamicDistTable tokens).decode br0 = some (0, br1) := by
  intro bitsTot lenTot bw' br0 br1
  have htable :=
    generatedDynamicDistTable_eq_matchTable_of_match_at
      tokens target len htarget ht
  have hmod : bitsTot % 2 = 0 := by
    simpa [bitsTot, Nat.shiftLeft_eq] using
      (Nat.mul_mod_right restBits (2 ^ 1))
  have hrow1 :
      generatedDynamicDistMatchTable.table[1]![bitsTot % 2]! = some 0 := by
    simpa [hmod] using generatedDynamicDistMatchTable_lookup_zero
  rw [htable]
  simpa [bitsTot, lenTot, bw', br0, br1] using
    generatedDynamicDistMatchTable_decode_zero_readerAt_writeBits
      bw bitsTot restLen hrow1 hbit hcur

/-- A generated distance-zero payload code decodes to distance value one. This
combines generic dynamic-Huffman distance-symbol decoding with the shared
DEFLATE distance decoder. -/
lemma generatedDynamicDistTable_decode_zero_distance_one_readerAt_writeBits
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (bw : Png.BitWriter) (tailBits tailLen : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := tailBits <<< 1
    let lenTot := 1 + tailLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br1 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 1)
      bw'.flush
      (by
        have hk : 1 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 1 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 1 hbit)
    ∃ hdist hbitsD,
      (generatedDynamicDistTable tokens).decode br0 = some (0, br1) ∧
      Png.decodeDistance 0 br1 hdist hbitsD = (1, br1) := by
  intro bitsTot lenTot bw' br0 br1
  have hdecode :=
    generatedDynamicDistTable_decode_zero_of_match_at_readerAt_writeBits
      tokens target len bw tailBits tailLen htarget ht hbit hcur
  have hdist : 0 < Png.distBases.size := by
    simpa [Png.distBases] using (Nat.succ_pos 29)
  have hbitsD :
      br1.bitIndex +
        Png.distExtra[0]'(by
          simpa [Png.distExtra] using (Nat.succ_pos 29)) ≤
        br1.data.size * 8 := by
    simpa [Png.distExtra] using Png.bitIndex_le_dataBits br1
  refine ⟨hdist, hbitsD, ?_, ?_⟩
  · simpa [bitsTot, lenTot, bw', br0, br1] using hdecode
  · exact Png.decodeDistance_zero br1 hbitsD

/-- The generated table spec reconstructed from generated lengths contains
exactly the named generated literal/length and distance tables. This is the
payload proof's bridge from header parsing to symbol decoding. -/
lemma generatedDynamicTableSpec_ofLengths?_eq_named
    (tokens : Array Png.DeflateToken) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let distLengths :=
      Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
    Png.DynamicTableSpec.ofLengths? litLenLengths distLengths =
      some
        { litLenLengths := litLenLengths
          distLengths := distLengths
          litLenTable := generatedDynamicLitLenTable tokens
          distTable := generatedDynamicDistTable tokens } := by
  intro litLenLengths distLengths
  exact Png.DynamicTableSpec.ofLengths?_mk
    (litLenLengths := litLenLengths) (distLengths := distLengths)
    (litLenTable := generatedDynamicLitLenTable tokens)
    (distTable := generatedDynamicDistTable tokens)
    (by simpa [litLenLengths] using
      mkHuffman_generatedDynamicLitLenLengths_eq tokens)
    (by simpa [distLengths] using
      buildDynamicDistTable_generatedDynamicDistLengths_eq tokens)

/-- Any spec accepted for the generated lengths is definitionally the named
generated table package. This makes later parser-produced witnesses stable
enough for payload replay. -/
lemma generatedDynamicTableSpec_eq_named_of_ofLengths?
    {tokens : Array Png.DeflateToken} {spec : Png.DynamicTableSpec}
    (h :
      Png.DynamicTableSpec.ofLengths?
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)) =
          some spec) :
    spec =
      { litLenLengths :=
          Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
        distLengths :=
          Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
        litLenTable := generatedDynamicLitLenTable tokens
        distTable := generatedDynamicDistTable tokens } := by
  have hnamed :=
    generatedDynamicTableSpec_ofLengths?_eq_named tokens
  simp only at hnamed
  rw [h] at hnamed
  injection hnamed

/-- The generated dynamic table package used by the full dynamic encoder. This
names the proof-side table spec shared by header parsing and payload replay. -/
def generatedDynamicTableSpec (tokens : Array Png.DeflateToken) :
    Png.DynamicTableSpec :=
  { litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    distLengths :=
      Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
    litLenTable := generatedDynamicLitLenTable tokens
    distTable := generatedDynamicDistTable tokens }

/-- Proof-facing bit width for one generated dynamic payload token. It mirrors
the literal/length code, optional length-extra bits, and distance code emitted
by `writeDynamicPayload`. -/
def dynamicPayloadTokenBitLen
    (litLenCodes distCodes : Array (Nat × Nat)) : Png.DeflateToken → Nat
  | .literal b => litLenCodes[b.toNat]!.2
  | .matchDist1 len =>
      let info := Png.fixedLenMatchInfo len
      litLenCodes[info.1]!.2 + info.2.2 + distCodes[0]!.2

/-- Proof-facing packed bits for one generated dynamic payload token. The low
bits are the literal/length code, followed by match extra bits and distance
code when the token is a distance-1 match. -/
def dynamicPayloadTokenBits
    (litLenCodes distCodes : Array (Nat × Nat)) : Png.DeflateToken → Nat
  | .literal b => litLenCodes[b.toNat]!.1
  | .matchDist1 len =>
      let info := Png.fixedLenMatchInfo len
      let litBits := litLenCodes[info.1]!.1
      let litLen := litLenCodes[info.1]!.2
      let extraBits := info.2.1
      let extraLen := info.2.2
      let distBits := distCodes[0]!.1
      litBits ||| (extraBits <<< litLen) |||
        (distBits <<< (litLen + extraLen))

/-- Proof-facing bit width of the generated dynamic payload terminator. -/
def dynamicPayloadEobBitLen (litLenCodes : Array (Nat × Nat)) : Nat :=
  litLenCodes[256]!.2

/-- Proof-facing packed bits of the generated dynamic payload terminator. -/
def dynamicPayloadEobBits (litLenCodes : Array (Nat × Nat)) : Nat :=
  litLenCodes[256]!.1

/-- Packed little-endian bit stream for generated dynamic payload tokens plus
the final EOB marker. This is the stream-level target for payload replay. -/
def dynamicPayloadStreamBits
    (litLenCodes distCodes : Array (Nat × Nat)) :
    List Png.DeflateToken → Nat
  | [] => dynamicPayloadEobBits litLenCodes
  | token :: tokens =>
      dynamicPayloadTokenBits litLenCodes distCodes token |||
        (dynamicPayloadStreamBits litLenCodes distCodes tokens <<<
          dynamicPayloadTokenBitLen litLenCodes distCodes token)

/-- Total bit width of the generated dynamic payload token stream plus EOB. -/
def dynamicPayloadStreamLen
    (litLenCodes distCodes : Array (Nat × Nat)) :
    List Png.DeflateToken → Nat
  | [] => dynamicPayloadEobBitLen litLenCodes
  | token :: tokens =>
      dynamicPayloadTokenBitLen litLenCodes distCodes token +
        dynamicPayloadStreamLen litLenCodes distCodes tokens

/-- Proof-facing expansion of payload tokens from a current decoded output.
It mirrors generic DEFLATE payload semantics for literals and distance-1
matches, and is the output target for generated dynamic traces. -/
def dynamicPayloadTraceOut (out : ByteArray) :
    List Png.DeflateToken → ByteArray
  | [] => out
  | Png.DeflateToken.literal b :: tokens =>
      dynamicPayloadTraceOut (out.push b) tokens
  | Png.DeflateToken.matchDist1 len :: tokens =>
      dynamicPayloadTraceOut
        (Png.pushRepeat out (out.get! (out.size - 1)) len) tokens

/-- Runtime-side precondition for replaying a generated token list from a
current output buffer. Each match token must have a byte to copy from. -/
def DynamicPayloadTraceOutputValid (out : ByteArray) :
    List Png.DeflateToken → Prop
  | [] => True
  | Png.DeflateToken.literal b :: tokens =>
      DynamicPayloadTraceOutputValid (out.push b) tokens
  | Png.DeflateToken.matchDist1 len :: tokens =>
      0 < out.size ∧
        DynamicPayloadTraceOutputValid
          (Png.pushRepeat out (out.get! (out.size - 1)) len) tokens

/-- List-shaped token expansion from an arbitrary output prefix. It is the
proof-facing counterpart of `deflateTokensExpand` for trace-output comparison. -/
def deflateTokensExpandListFrom (out : ByteArray) :
    List Png.DeflateToken → ByteArray
  | [] => out
  | token :: tokens =>
      deflateTokensExpandListFrom (Png.deflateTokenExpand out token) tokens

/-- Trace output composes across list append. This is the basic transport fact
for accumulator-style tokenizers that append to an existing token prefix. -/
lemma dynamicPayloadTraceOut_append
    (out : ByteArray) (xs ys : List Png.DeflateToken) :
    dynamicPayloadTraceOut out (xs ++ ys) =
      dynamicPayloadTraceOut (dynamicPayloadTraceOut out xs) ys := by
  induction xs generalizing out with
  | nil =>
      simp [dynamicPayloadTraceOut]
  | cons token xs ih =>
      cases token with
      | literal b =>
          simp [dynamicPayloadTraceOut, ih]
      | matchDist1 len =>
          simp [dynamicPayloadTraceOut, ih]

/-- Trace-output validity composes across list append. The suffix starts from
the output produced by replaying the prefix. -/
lemma DynamicPayloadTraceOutputValid_append
    (out : ByteArray) (xs ys : List Png.DeflateToken) :
    DynamicPayloadTraceOutputValid out (xs ++ ys) ↔
      DynamicPayloadTraceOutputValid out xs ∧
        DynamicPayloadTraceOutputValid
          (dynamicPayloadTraceOut out xs) ys := by
  induction xs generalizing out with
  | nil =>
      simp [DynamicPayloadTraceOutputValid, dynamicPayloadTraceOut]
  | cons token xs ih =>
      cases token with
      | literal b =>
          simp [DynamicPayloadTraceOutputValid, dynamicPayloadTraceOut, ih]
      | matchDist1 len =>
          simp [DynamicPayloadTraceOutputValid, dynamicPayloadTraceOut, ih,
            and_assoc]

/-- Appending a literal token preserves replay validity because literals do not
need a prior byte. This is the literal-push step for accumulator proofs. -/
lemma DynamicPayloadTraceOutputValid_array_push_literal
    (out : ByteArray) (tokens : Array Png.DeflateToken) (b : UInt8)
    (hvalid : DynamicPayloadTraceOutputValid out tokens.toList) :
    DynamicPayloadTraceOutputValid out
      (tokens.push (Png.DeflateToken.literal b)).toList := by
  rw [Array.toList_push, DynamicPayloadTraceOutputValid_append]
  exact ⟨hvalid, by simp [DynamicPayloadTraceOutputValid]⟩

/-- Replaying an array with one appended literal is replaying the prefix and
then pushing that literal byte. -/
lemma dynamicPayloadTraceOut_array_push_literal
    (out : ByteArray) (tokens : Array Png.DeflateToken) (b : UInt8) :
    dynamicPayloadTraceOut out
      (tokens.push (Png.DeflateToken.literal b)).toList =
        (dynamicPayloadTraceOut out tokens.toList).push b := by
  rw [Array.toList_push, dynamicPayloadTraceOut_append]
  simp [dynamicPayloadTraceOut]

/-- Appending a distance-1 match preserves replay validity when the replayed
prefix has a byte available to copy. -/
lemma DynamicPayloadTraceOutputValid_array_push_matchDist1
    (out : ByteArray) (tokens : Array Png.DeflateToken) (len : Nat)
    (hvalid : DynamicPayloadTraceOutputValid out tokens.toList)
    (hout : 0 < (dynamicPayloadTraceOut out tokens.toList).size) :
    DynamicPayloadTraceOutputValid out
      (tokens.push (Png.DeflateToken.matchDist1 len)).toList := by
  rw [Array.toList_push, DynamicPayloadTraceOutputValid_append]
  exact ⟨hvalid, by simpa [DynamicPayloadTraceOutputValid] using hout⟩

/-- Replaying an array with one appended distance-1 match repeats the last
prefix byte by the match length. -/
lemma dynamicPayloadTraceOut_array_push_matchDist1
    (out : ByteArray) (tokens : Array Png.DeflateToken) (len : Nat) :
    dynamicPayloadTraceOut out
      (tokens.push (Png.DeflateToken.matchDist1 len)).toList =
        Png.pushRepeat (dynamicPayloadTraceOut out tokens.toList)
          ((dynamicPayloadTraceOut out tokens.toList).get!
            ((dynamicPayloadTraceOut out tokens.toList).size - 1)) len := by
  rw [Array.toList_push, dynamicPayloadTraceOut_append]
  simp [dynamicPayloadTraceOut]

/-- Repeated literal-token appends preserve replay validity. This covers the
short-run branch of the generated dynamic tokenizer. -/
lemma DynamicPayloadTraceOutputValid_pushLiteralRepeat
    (out : ByteArray) (tokens : Array Png.DeflateToken) (b : UInt8) (n : Nat)
    (hvalid : DynamicPayloadTraceOutputValid out tokens.toList) :
    DynamicPayloadTraceOutputValid out
      (Png.pushLiteralRepeat tokens b n).toList := by
  induction n generalizing tokens with
  | zero =>
      simpa [Png.pushLiteralRepeat] using hvalid
  | succ n ih =>
      exact ih (tokens.push (Png.DeflateToken.literal b))
        (DynamicPayloadTraceOutputValid_array_push_literal out tokens b hvalid)

/-- Distance-1 match chunks preserve replay validity once the current replay
output is nonempty. This covers the long-run match suffix. -/
lemma DynamicPayloadTraceOutputValid_deflateMatchDist1Chunks
    (out : ByteArray) (tokens : Array Png.DeflateToken) (remaining : Nat)
    (hvalid : DynamicPayloadTraceOutputValid out tokens.toList)
    (hout : 0 < (dynamicPayloadTraceOut out tokens.toList).size) :
    DynamicPayloadTraceOutputValid out
      (Png.deflateMatchDist1Chunks tokens remaining).toList := by
  induction remaining using Nat.strong_induction_on generalizing tokens with
  | h remaining ih =>
      by_cases hrem : 3 ≤ remaining
      · let chunk := Png.chooseFixedMatchChunkLen remaining
        have hpush :
            DynamicPayloadTraceOutputValid out
              (tokens.push (Png.DeflateToken.matchDist1 chunk)).toList :=
          DynamicPayloadTraceOutputValid_array_push_matchDist1
            out tokens chunk hvalid hout
        have houtPush :
            0 <
              (dynamicPayloadTraceOut out
                (tokens.push (Png.DeflateToken.matchDist1 chunk)).toList).size := by
          rw [dynamicPayloadTraceOut_array_push_matchDist1]
          exact Png.pushRepeat_pos (dynamicPayloadTraceOut out tokens.toList)
            ((dynamicPayloadTraceOut out tokens.toList).get!
              ((dynamicPayloadTraceOut out tokens.toList).size - 1)) chunk hout
        have hlt : remaining - chunk < remaining := by
          simpa [chunk] using
            Png.chooseFixedMatchChunkLen_sub_lt remaining hrem
        have hih :=
          ih (remaining - chunk) hlt
            (tokens.push (Png.DeflateToken.matchDist1 chunk)) hpush houtPush
        rw [deflateMatchDist1Chunks_of_ge3 tokens remaining hrem]
        simpa [chunk] using hih
      · rw [deflateMatchDist1Chunks_of_lt3 tokens remaining hrem]
        exact hvalid

/-- The generated tokenizer preserves replay validity from any valid token
prefix. This follows the same accumulator recursion as tokenizer expansion. -/
lemma DynamicPayloadTraceOutputValid_deflateTokensDist1Aux
    (data : Array UInt8) (i : Nat) (tokens : Array Png.DeflateToken)
    (hvalid : DynamicPayloadTraceOutputValid ByteArray.empty tokens.toList) :
    DynamicPayloadTraceOutputValid ByteArray.empty
      (Png.deflateTokensDist1Aux data i tokens).toList := by
  rw [Png.deflateTokensDist1Aux.eq_1]
  by_cases hlt : i < data.size
  · let b := data[i]
    let j := Png.sameByteRunEndFast data b (i + 1)
    let runLen := j - i
    let tokens' :=
      if 4 ≤ runLen then
        Png.deflateMatchDist1Chunks
          (tokens.push (Png.DeflateToken.literal b)) (runLen - 1)
      else
        Png.pushLiteralRepeat tokens b runLen
    have htokens' :
        DynamicPayloadTraceOutputValid ByteArray.empty tokens'.toList := by
      by_cases h4 : 4 ≤ runLen
      · have hpushLit :
            DynamicPayloadTraceOutputValid ByteArray.empty
              (tokens.push (Png.DeflateToken.literal b)).toList :=
          DynamicPayloadTraceOutputValid_array_push_literal
            ByteArray.empty tokens b hvalid
        have houtLit :
            0 <
              (dynamicPayloadTraceOut ByteArray.empty
                (tokens.push (Png.DeflateToken.literal b)).toList).size := by
          rw [dynamicPayloadTraceOut_array_push_literal]
          simp
        have hchunks :=
          DynamicPayloadTraceOutputValid_deflateMatchDist1Chunks
            ByteArray.empty (tokens.push (Png.DeflateToken.literal b))
            (runLen - 1) hpushLit houtLit
        simpa [tokens', h4] using hchunks
      · have hlits :=
          DynamicPayloadTraceOutputValid_pushLiteralRepeat
            ByteArray.empty tokens b runLen hvalid
        simpa [tokens', h4] using hlits
    have hrec :=
      DynamicPayloadTraceOutputValid_deflateTokensDist1Aux data j tokens' htokens'
    simpa [hlt, b, j, runLen, tokens'] using hrec
  · simp [hlt, hvalid]
termination_by data.size - i
decreasing_by
  have hgt : i < Png.sameByteRunEndFast data data[i] (i + 1) := by
    exact sameByteRunEndFast_gt_prev data i hlt
  have hle : Png.sameByteRunEndFast data data[i] (i + 1) ≤ data.size := by
    exact sameByteRunEndFast_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  exact (by omega :
    data.size - Png.sameByteRunEndFast data data[i] (i + 1) < data.size - i)

/-- Tokens emitted by the public generated dynamic tokenizer can be replayed
from an empty output buffer without an invalid distance-1 match. -/
lemma DynamicPayloadTraceOutputValid_deflateTokensDist1 (raw : ByteArray) :
    DynamicPayloadTraceOutputValid ByteArray.empty
      (Png.deflateTokensDist1 raw).toList := by
  simpa [Png.deflateTokensDist1] using
    DynamicPayloadTraceOutputValid_deflateTokensDist1Aux raw.data 0 #[]
      (by simp [DynamicPayloadTraceOutputValid])

/-- Recursive list expansion is the same as list `foldl` with
`deflateTokenExpand`. This connects proof-facing list replay to arrays. -/
lemma deflateTokensExpandListFrom_eq_foldl
    (out : ByteArray) (tokens : List Png.DeflateToken) :
    deflateTokensExpandListFrom out tokens =
      tokens.foldl Png.deflateTokenExpand out := by
  induction tokens generalizing out with
  | nil =>
      simp [deflateTokensExpandListFrom]
  | cons token tokens ih =>
      simp [deflateTokensExpandListFrom, ih]

/-- Array token expansion is proof-facing list expansion over `Array.toList`.
This bridges `deflateTokensExpand` to trace-output replay. -/
lemma deflateTokensExpand_eq_deflateTokensExpandListFrom
    (tokens : Array Png.DeflateToken) :
    Png.deflateTokensExpand tokens =
      deflateTokensExpandListFrom ByteArray.empty tokens.toList := by
  simp [Png.deflateTokensExpand, Array.foldl_toList,
    deflateTokensExpandListFrom_eq_foldl]

/-- On replay-valid token lists, proof-facing trace output agrees with
`deflateTokenExpand` semantics. The match case uses the prior-byte validity
condition to remove `deflateTokenExpand`'s empty-output guard. -/
lemma dynamicPayloadTraceOut_eq_deflateTokensExpandListFrom_of_valid
    (out : ByteArray) (tokens : List Png.DeflateToken)
    (hvalid : DynamicPayloadTraceOutputValid out tokens) :
    dynamicPayloadTraceOut out tokens =
      deflateTokensExpandListFrom out tokens := by
  induction tokens generalizing out with
  | nil =>
      simp [dynamicPayloadTraceOut, deflateTokensExpandListFrom]
  | cons token tokens ih =>
      cases token with
      | literal b =>
          have htail :
              DynamicPayloadTraceOutputValid (out.push b) tokens := by
            simpa [DynamicPayloadTraceOutputValid] using hvalid
          simpa [dynamicPayloadTraceOut, deflateTokensExpandListFrom,
            Png.deflateTokenExpand] using ih (out.push b) htail
      | matchDist1 len =>
          have hout : 0 < out.size := by
            simpa [DynamicPayloadTraceOutputValid] using hvalid.1
          have htail :
              DynamicPayloadTraceOutputValid
                (Png.pushRepeat out (out.get! (out.size - 1)) len) tokens := by
            simpa [DynamicPayloadTraceOutputValid] using hvalid.2
          have htoken :
              Png.deflateTokenExpand out (Png.DeflateToken.matchDist1 len) =
                Png.pushRepeat out (out.get! (out.size - 1)) len := by
            calc
              Png.deflateTokenExpand out (Png.DeflateToken.matchDist1 len) =
                  Png.pushByteRepeat out (out.get! (out.size - 1)) len := by
                    exact deflateTokenExpand_matchDist1_of_pos out len hout
              _ = Png.pushRepeat out (out.get! (out.size - 1)) len := by
                    rw [pushByteRepeat_eq_pushRepeat]
          simpa [dynamicPayloadTraceOut, deflateTokensExpandListFrom, htoken]
            using
              ih (Png.pushRepeat out (out.get! (out.size - 1)) len) htail

/-- Replaying the public generated dynamic tokenizer yields exactly the source
bytes. This is the output side of the generated payload trace bridge. -/
lemma dynamicPayloadTraceOut_deflateTokensDist1_eq (raw : ByteArray) :
    dynamicPayloadTraceOut ByteArray.empty
      (Png.deflateTokensDist1 raw).toList = raw := by
  have hvalid := DynamicPayloadTraceOutputValid_deflateTokensDist1 raw
  calc
    dynamicPayloadTraceOut ByteArray.empty
        (Png.deflateTokensDist1 raw).toList =
      deflateTokensExpandListFrom ByteArray.empty
        (Png.deflateTokensDist1 raw).toList := by
        exact dynamicPayloadTraceOut_eq_deflateTokensExpandListFrom_of_valid
          ByteArray.empty (Png.deflateTokensDist1 raw).toList hvalid
    _ = Png.deflateTokensExpand (Png.deflateTokensDist1 raw) := by
        exact (deflateTokensExpand_eq_deflateTokensExpandListFrom
          (Png.deflateTokensDist1 raw)).symm
    _ = raw := deflateTokensExpand_deflateTokensDist1 raw

/-- Generated payload EOB is emitted with the generated nine-bit
literal/length code. This is the terminal width used by payload traces. -/
lemma dynamicPayloadEobBitLen_generated_eq_nine
    (tokens : Array Png.DeflateToken) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    dynamicPayloadEobBitLen litLenCodes = 9 := by
  intro litLenCodes
  simpa [dynamicPayloadEobBitLen, litLenCodes] using
    generatedDynamicLitLenCodes_eob_len_eq_nine tokens

/-- A generated literal payload token uses the generated nine-bit
literal/length row. This links token frequency collection to the payload
writer's literal branch. -/
lemma dynamicPayloadTokenBitLen_generated_literal_eq_nine_at
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))
    dynamicPayloadTokenBitLen litLenCodes distCodes
      (Png.DeflateToken.literal b) = 9 := by
  intro litLenCodes distCodes
  simpa [dynamicPayloadTokenBitLen, litLenCodes] using
    generatedDynamicLitLenCodes_literal_len_eq_nine_at
      tokens target b htarget ht

/-- A generated match payload token uses a nine-bit literal/length symbol,
the DEFLATE match extra bits, and the generated one-bit distance-zero code. -/
lemma dynamicPayloadTokenBitLen_generated_match_eq
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))
    dynamicPayloadTokenBitLen litLenCodes distCodes
      (Png.DeflateToken.matchDist1 len) =
        9 + (Png.fixedLenMatchInfo len).2.2 + 1 := by
  intro litLenCodes distCodes
  have hlit :=
    generatedDynamicLitLenCodes_match_len_eq_nine_at
      tokens target len htarget ht hlen
  have hdist :=
    generatedDynamicDistCodes_zero_len_eq_one_of_match_at
      tokens target len htarget ht
  simpa [dynamicPayloadTokenBitLen, litLenCodes, distCodes,
    Nat.add_assoc] using congrArg₂ Nat.add hlit (congrArg₂ Nat.add rfl hdist)

/-- Generated payload EOB bits fit in the EOB code width. This is the
terminal code-space guard needed by writer concatenation proofs. -/
lemma dynamicPayloadEobBits_generated_lt_codeSpace
    (tokens : Array Png.DeflateToken) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    dynamicPayloadEobBits litLenCodes <
      2 ^ dynamicPayloadEobBitLen litLenCodes := by
  intro litLenCodes
  have hbits := generatedDynamicLitLenCodes_eob_bits_lt_codeSpace tokens
  have hlen := dynamicPayloadEobBitLen_generated_eq_nine tokens
  simpa [dynamicPayloadEobBits, litLenCodes, hlen] using hbits

/-- Generated literal payload bits fit in the literal token width. This is the
literal branch's code-space guard for payload writer replay. -/
lemma dynamicPayloadTokenBits_generated_literal_lt_codeSpace_at
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))
    dynamicPayloadTokenBits litLenCodes distCodes
      (Png.DeflateToken.literal b) <
        2 ^ dynamicPayloadTokenBitLen litLenCodes distCodes
          (Png.DeflateToken.literal b) := by
  intro litLenCodes distCodes
  have hbits :=
    generatedDynamicLitLenCodes_literal_bits_lt_codeSpace_at
      tokens target b htarget ht
  have hcodeLen :=
    generatedDynamicLitLenCodes_literal_len_eq_nine_at
      tokens target b htarget ht
  simpa [dynamicPayloadTokenBits, dynamicPayloadTokenBitLen,
    litLenCodes, distCodes, hcodeLen] using hbits

/-- Generated match payload bits fit in the match token width. This combines
the generated nine-bit length symbol, DEFLATE length-extra bits, and generated
one-bit distance symbol for writer replay. -/
lemma dynamicPayloadTokenBits_generated_match_lt_codeSpace_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))
    dynamicPayloadTokenBits litLenCodes distCodes
      (Png.DeflateToken.matchDist1 len) <
        2 ^ dynamicPayloadTokenBitLen litLenCodes distCodes
          (Png.DeflateToken.matchDist1 len) := by
  intro litLenCodes distCodes
  rcases hinfo : Png.fixedLenMatchInfo len with ⟨sym, extraBits, extraLen⟩
  have hlitBits :
      litLenCodes[sym]!.1 < 2 ^ 9 := by
    have h :=
      generatedDynamicLitLenCodes_match_bits_lt_codeSpace_at
        tokens target len htarget ht hlen
    simpa [litLenCodes, Png.generatedDynamicLitLenCodeLen, hinfo] using h
  have hlitLen :
      litLenCodes[sym]!.2 = 9 := by
    have h :=
      generatedDynamicLitLenCodes_match_len_eq_nine_at
        tokens target len htarget ht hlen
    simpa [litLenCodes, hinfo] using h
  have hdistBits :
      distCodes[0]!.1 < 2 := by
    simpa [distCodes] using
      generatedDynamicDistCodes_zero_bits_lt_two_of_match_at
        tokens target len htarget ht
  have hdistLen :
      distCodes[0]!.2 = 1 := by
    simpa [distCodes] using
      generatedDynamicDistCodes_zero_len_eq_one_of_match_at
        tokens target len htarget ht
  have hextraBits : extraBits < 2 ^ extraLen := by
    have hspec := Png.fixedLenMatchInfo_spec_internal len hlen.1 hlen.2
    rw [hinfo] at hspec
    rcases hspec with
      ⟨_hsym, _hidxBase, _hidxExtra, _hextra, _hbase, hbits⟩
    exact hbits
  have hextraShift :
      extraBits <<< 9 < 2 ^ (extraLen + 9) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos 9)).mpr hextraBits
  have hlitWide :
      litLenCodes[sym]!.1 < 2 ^ (extraLen + 9) := by
    exact lt_of_lt_of_le hlitBits
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hprefix :
      litLenCodes[sym]!.1 ||| (extraBits <<< 9) <
        2 ^ (extraLen + 9) :=
    Nat.or_lt_two_pow hlitWide hextraShift
  have hdistShift :
      distCodes[0]!.1 <<< (9 + extraLen) <
        2 ^ (1 + (9 + extraLen)) := by
    rw [Nat.shiftLeft_eq]
    calc
      distCodes[0]!.1 * 2 ^ (9 + extraLen)
          < 2 * 2 ^ (9 + extraLen) :=
      (Nat.mul_lt_mul_right (Nat.two_pow_pos (9 + extraLen))).mpr
        (by simpa using hdistBits)
      _ = 2 ^ (1 + (9 + extraLen)) := by
        calc
          2 * 2 ^ (9 + extraLen)
              = 2 ^ (9 + extraLen) * 2 := by
                rw [Nat.mul_comm]
          _ = 2 ^ ((9 + extraLen) + 1) := by
                simpa using (Nat.pow_succ 2 (9 + extraLen)).symm
          _ = 2 ^ (1 + (9 + extraLen)) := by
                rw [Nat.add_comm]
  have hprefixWide :
      litLenCodes[sym]!.1 ||| (extraBits <<< 9) <
        2 ^ (1 + (9 + extraLen)) := by
    exact lt_of_lt_of_le hprefix
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hor :
      (litLenCodes[sym]!.1 ||| (extraBits <<< 9)) |||
          (distCodes[0]!.1 <<< (9 + extraLen)) <
        2 ^ (1 + (9 + extraLen)) :=
    Nat.or_lt_two_pow hprefixWide hdistShift
  simpa [dynamicPayloadTokenBits, dynamicPayloadTokenBitLen,
    litLenCodes, distCodes, hinfo, hlitLen, hdistLen,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.or_assoc] using hor

/-- Proof-facing list writer for generated dynamic payload tokens. It mirrors
the runtime payload loop while exposing a structural induction principle. -/
def writeDynamicPayloadToken
    (bw : Png.BitWriter) (litLenCodes distCodes : Array (Nat × Nat)) :
    Png.DeflateToken → Png.BitWriter
  | .literal b =>
      bw.writeRevCode litLenCodes b.toNat
  | .matchDist1 len =>
      let (sym, extraBits, extraLen) := Png.fixedLenMatchInfo len
      let bw := bw.writeRevCode litLenCodes sym
      let bw := bw.writeBitsFast extraBits extraLen
      bw.writeRevCode distCodes 0

/-- A literal payload-token write is exactly a write of the packed
literal/length code. This removes the runtime `writeRevCode` wrapper from
literal replay proofs. -/
lemma writeDynamicPayloadToken_literal_eq_writeBits
    (bw : Png.BitWriter) (litLenCodes distCodes : Array (Nat × Nat))
    (b : UInt8) :
    writeDynamicPayloadToken bw litLenCodes distCodes
        (Png.DeflateToken.literal b) =
      Png.BitWriter.writeBits bw
        (dynamicPayloadTokenBits litLenCodes distCodes
          (Png.DeflateToken.literal b))
        (dynamicPayloadTokenBitLen litLenCodes distCodes
          (Png.DeflateToken.literal b)) := by
  simp [writeDynamicPayloadToken, dynamicPayloadTokenBits,
    dynamicPayloadTokenBitLen, Png.BitWriter.writeRevCode,
    Png.writeBitsFast_eq_writeBits]

/-- An EOB payload write is exactly a write of the packed EOB code. This is
the terminal writer bridge for generated payload replay. -/
lemma writeDynamicPayloadEob_eq_writeBits
    (bw : Png.BitWriter) (litLenCodes : Array (Nat × Nat)) :
    bw.writeRevCode litLenCodes 256 =
      Png.BitWriter.writeBits bw
        (dynamicPayloadEobBits litLenCodes)
        (dynamicPayloadEobBitLen litLenCodes) := by
  simp [dynamicPayloadEobBits, dynamicPayloadEobBitLen,
    Png.BitWriter.writeRevCode, Png.writeBitsFast_eq_writeBits]

/-- A generated match payload-token write is exactly a write of the packed
match bits. This bridges the runtime three-write match branch to the stream
shape consumed by the generic dynamic decoder proof. -/
lemma writeDynamicPayloadToken_generated_match_eq_writeBits_at
    (bw : Png.BitWriter) (tokens : Array Png.DeflateToken)
    (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))
    writeDynamicPayloadToken bw litLenCodes distCodes
        (Png.DeflateToken.matchDist1 len) =
      Png.BitWriter.writeBits bw
        (dynamicPayloadTokenBits litLenCodes distCodes
          (Png.DeflateToken.matchDist1 len))
        (dynamicPayloadTokenBitLen litLenCodes distCodes
          (Png.DeflateToken.matchDist1 len)) := by
  intro litLenCodes distCodes
  rcases hinfo : Png.fixedLenMatchInfo len with ⟨sym, extraBits, extraLen⟩
  have hlitBits9 :
      litLenCodes[sym]!.1 < 2 ^ 9 := by
    have h :=
      generatedDynamicLitLenCodes_match_bits_lt_codeSpace_at
        tokens target len htarget ht hlen
    simpa [litLenCodes, Png.generatedDynamicLitLenCodeLen, hinfo] using h
  have hlitLen :
      litLenCodes[sym]!.2 = 9 := by
    have h :=
      generatedDynamicLitLenCodes_match_len_eq_nine_at
        tokens target len htarget ht hlen
    simpa [litLenCodes, hinfo] using h
  have hdistLen :
      distCodes[0]!.2 = 1 := by
    simpa [distCodes] using
      generatedDynamicDistCodes_zero_len_eq_one_of_match_at
        tokens target len htarget ht
  have hextraBits : extraBits < 2 ^ extraLen := by
    have hspec := Png.fixedLenMatchInfo_spec_internal len hlen.1 hlen.2
    rw [hinfo] at hspec
    rcases hspec with
      ⟨_hsym, _hidxBase, _hidxExtra, _hextra, _hbase, hbits⟩
    exact hbits
  have hlitBits :
      litLenCodes[sym]!.1 < 2 ^ litLenCodes[sym]!.2 := by
    simpa [hlitLen] using hlitBits9
  have hextraShift :
      extraBits <<< 9 < 2 ^ (extraLen + 9) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos 9)).mpr hextraBits
  have hlitWide :
      litLenCodes[sym]!.1 < 2 ^ (extraLen + 9) := by
    exact lt_of_lt_of_le hlitBits9
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hprefix9 :
      litLenCodes[sym]!.1 ||| (extraBits <<< 9) <
        2 ^ (extraLen + 9) :=
    Nat.or_lt_two_pow hlitWide hextraShift
  have hprefix :
      litLenCodes[sym]!.1 ||| (extraBits <<< litLenCodes[sym]!.2) <
        2 ^ (litLenCodes[sym]!.2 + extraLen) := by
    simpa [hlitLen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hprefix9
  have hconcatLit :
      Png.BitWriter.writeBits bw
          (litLenCodes[sym]!.1 |||
            (extraBits <<< litLenCodes[sym]!.2))
          (litLenCodes[sym]!.2 + extraLen) =
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw litLenCodes[sym]!.1
            litLenCodes[sym]!.2)
          extraBits extraLen :=
    Png.writeBits_concat bw litLenCodes[sym]!.1 extraBits
      litLenCodes[sym]!.2 extraLen hlitBits
  have hconcatDist :
      Png.BitWriter.writeBits bw
          ((litLenCodes[sym]!.1 |||
              (extraBits <<< litLenCodes[sym]!.2)) |||
            (distCodes[0]!.1 <<<
              (litLenCodes[sym]!.2 + extraLen)))
          ((litLenCodes[sym]!.2 + extraLen) + distCodes[0]!.2) =
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw
            (litLenCodes[sym]!.1 |||
              (extraBits <<< litLenCodes[sym]!.2))
            (litLenCodes[sym]!.2 + extraLen))
          distCodes[0]!.1 distCodes[0]!.2 :=
    Png.writeBits_concat bw
      (litLenCodes[sym]!.1 ||| (extraBits <<< litLenCodes[sym]!.2))
      distCodes[0]!.1 (litLenCodes[sym]!.2 + extraLen)
      distCodes[0]!.2 hprefix
  calc
    writeDynamicPayloadToken bw litLenCodes distCodes
        (Png.DeflateToken.matchDist1 len)
        =
      Png.BitWriter.writeBits
        (Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw litLenCodes[sym]!.1
            litLenCodes[sym]!.2)
          extraBits extraLen)
        distCodes[0]!.1 distCodes[0]!.2 := by
          simp [writeDynamicPayloadToken, Png.BitWriter.writeRevCode,
            Png.writeBitsFast_eq_writeBits, hinfo]
    _ =
      Png.BitWriter.writeBits
        (Png.BitWriter.writeBits bw
          (litLenCodes[sym]!.1 |||
            (extraBits <<< litLenCodes[sym]!.2))
          (litLenCodes[sym]!.2 + extraLen))
        distCodes[0]!.1 distCodes[0]!.2 := by
          rw [hconcatLit]
    _ =
      Png.BitWriter.writeBits bw
        ((litLenCodes[sym]!.1 |||
            (extraBits <<< litLenCodes[sym]!.2)) |||
          (distCodes[0]!.1 <<<
            (litLenCodes[sym]!.2 + extraLen)))
        ((litLenCodes[sym]!.2 + extraLen) + distCodes[0]!.2) := by
          rw [hconcatDist]
    _ =
      Png.BitWriter.writeBits bw
        (dynamicPayloadTokenBits litLenCodes distCodes
          (Png.DeflateToken.matchDist1 len))
        (dynamicPayloadTokenBitLen litLenCodes distCodes
          (Png.DeflateToken.matchDist1 len)) := by
          simp [dynamicPayloadTokenBits, dynamicPayloadTokenBitLen,
            hinfo, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
            Nat.or_assoc]

/-- Proof-facing list writer for generated dynamic payload tokens. It mirrors
the runtime payload loop while exposing a structural induction principle. -/
def writeDynamicPayloadTokensList
    (bw : Png.BitWriter) (litLenCodes distCodes : Array (Nat × Nat)) :
    List Png.DeflateToken → Png.BitWriter
  | [] => bw.writeRevCode litLenCodes 256
  | token :: tokens =>
      writeDynamicPayloadTokensList
        (writeDynamicPayloadToken bw litLenCodes distCodes token)
        litLenCodes distCodes tokens

/-- The fold produced by Lean's `forIn` elaboration reduces to the
proof-facing recursive list writer. -/
private lemma writeDynamicPayloadTokensList_foldl
    (bw : Png.BitWriter) (tokens : List Png.DeflateToken)
    (litLenCodes distCodes : Array (Nat × Nat)) :
    (List.foldl
        (fun acc token => writeDynamicPayloadToken acc litLenCodes distCodes token)
        bw tokens).writeRevCode litLenCodes 256 =
      writeDynamicPayloadTokensList bw litLenCodes distCodes tokens := by
  induction tokens generalizing bw with
  | nil =>
      simp [writeDynamicPayloadTokensList]
  | cons token tokens ih =>
      simp [writeDynamicPayloadTokensList, ih]

/-- The list `forIn` loop generated by the runtime payload writer reduces to
the proof-facing recursive list writer. -/
private lemma writeDynamicPayloadTokensList_forIn
    (bw : Png.BitWriter) (tokens : List Png.DeflateToken)
    (litLenCodes distCodes : Array (Nat × Nat)) :
    (Id.run <|
      forIn (m := Id) tokens bw fun token r =>
        pure (ForInStep.yield
          (writeDynamicPayloadToken r litLenCodes distCodes token))).writeRevCode
      litLenCodes 256 =
      writeDynamicPayloadTokensList bw litLenCodes distCodes tokens := by
  simpa using
    writeDynamicPayloadTokensList_foldl bw tokens litLenCodes distCodes

/-- The runtime array payload writer is the proof-facing list writer over
`Array.toList`. This bridges `Png.writeDynamicPayload` to stream replay. -/
lemma writeDynamicPayload_eq_writeDynamicPayloadTokensList
    (bw : Png.BitWriter) (tokens : Array Png.DeflateToken)
    (litLenCodes distCodes : Array (Nat × Nat)) :
    Png.writeDynamicPayload bw tokens litLenCodes distCodes =
      writeDynamicPayloadTokensList bw litLenCodes distCodes tokens.toList := by
  cases tokens with
  | mk data =>
      induction data generalizing bw with
      | nil =>
          simp [Png.writeDynamicPayload, writeDynamicPayloadTokensList]
      | cons token data ih =>
          cases token with
          | literal b =>
              simpa [Png.writeDynamicPayload, writeDynamicPayloadTokensList,
                writeDynamicPayloadToken] using
                ih (bw.writeRevCode litLenCodes b.toNat)
          | matchDist1 len =>
              simpa [Png.writeDynamicPayload, writeDynamicPayloadTokensList,
                writeDynamicPayloadToken] using
                ih
                  (((bw.writeRevCode litLenCodes
                    (Png.fixedLenMatchInfo len).1).writeBits
                    (Png.fixedLenMatchInfo len).2.1
                    (Png.fixedLenMatchInfo len).2.2).writeRevCode
                    distCodes 0)

/-- A token found in an array's `toList` has a corresponding array index. This
feeds list-level payload replay with the indexed facts used by generated table
proofs. -/
lemma deflateToken_mem_toList_index
    {tokens : Array Png.DeflateToken} {token : Png.DeflateToken}
    (hmem : token ∈ tokens.toList) :
    ∃ target, ∃ htarget : target < tokens.size,
      tokens[target]'htarget = token := by
  rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, hget⟩
  have hidxArray : idx < tokens.size := by
    simpa using hidx
  have htoken : tokens[idx] = token := by
    simpa using hget
  exact ⟨idx, hidxArray, by simpa using htoken⟩

/-- A generated payload-token list writes exactly its packed payload stream.
The membership hypothesis connects each list token back to the source array
that generated the Huffman tables. -/
lemma writeDynamicPayloadTokensList_generated_eq_writeBits
    (source : Array Png.DeflateToken) (tokens : List Png.DeflateToken)
    (hvalid : DeflateTokensMatchLengthsValid source)
    (hmember :
      ∀ token ∈ tokens, ∃ target, ∃ htarget : target < source.size,
        source[target]'htarget = token)
    (bw : Png.BitWriter) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs source))
    writeDynamicPayloadTokensList bw litLenCodes distCodes tokens =
      Png.BitWriter.writeBits bw
        (dynamicPayloadStreamBits litLenCodes distCodes tokens)
        (dynamicPayloadStreamLen litLenCodes distCodes tokens) := by
  revert bw hmember
  induction tokens with
  | nil =>
      intro _hmember bw litLenCodes distCodes
      simpa [writeDynamicPayloadTokensList, dynamicPayloadStreamBits,
        dynamicPayloadStreamLen] using
        writeDynamicPayloadEob_eq_writeBits bw litLenCodes
  | cons token tokens ih =>
      intro hmember bw litLenCodes distCodes
      have htailMember :
          ∀ t ∈ tokens, ∃ target, ∃ htarget : target < source.size,
            source[target]'htarget = t := by
        intro t ht
        exact hmember t (List.mem_cons_of_mem token ht)
      have htokenWrite :
          writeDynamicPayloadToken bw litLenCodes distCodes token =
            Png.BitWriter.writeBits bw
              (dynamicPayloadTokenBits litLenCodes distCodes token)
              (dynamicPayloadTokenBitLen litLenCodes distCodes token) := by
        cases token with
        | literal b =>
            exact writeDynamicPayloadToken_literal_eq_writeBits
              bw litLenCodes distCodes b
        | matchDist1 len =>
            rcases hmember (Png.DeflateToken.matchDist1 len) (by simp) with
              ⟨target, htarget, ht⟩
            have hlen := hvalid target len htarget ht
            simpa [litLenCodes, distCodes] using
              writeDynamicPayloadToken_generated_match_eq_writeBits_at
                (bw := bw) (tokens := source) (target := target)
                (len := len) htarget ht hlen
      have htokenBits :
          dynamicPayloadTokenBits litLenCodes distCodes token <
            2 ^ dynamicPayloadTokenBitLen litLenCodes distCodes token := by
        cases token with
        | literal b =>
            rcases hmember (Png.DeflateToken.literal b) (by simp) with
              ⟨target, htarget, ht⟩
            simpa [litLenCodes, distCodes] using
              dynamicPayloadTokenBits_generated_literal_lt_codeSpace_at
                source target b htarget ht
        | matchDist1 len =>
            rcases hmember (Png.DeflateToken.matchDist1 len) (by simp) with
              ⟨target, htarget, ht⟩
            have hlen := hvalid target len htarget ht
            simpa [litLenCodes, distCodes] using
              dynamicPayloadTokenBits_generated_match_lt_codeSpace_at
                source target len htarget ht hlen
      have htailWrite :=
        ih
          htailMember
          (Png.BitWriter.writeBits bw
            (dynamicPayloadTokenBits litLenCodes distCodes token)
            (dynamicPayloadTokenBitLen litLenCodes distCodes token))
      have htailWrite' :
          writeDynamicPayloadTokensList
              (Png.BitWriter.writeBits bw
                (dynamicPayloadTokenBits litLenCodes distCodes token)
                (dynamicPayloadTokenBitLen litLenCodes distCodes token))
              litLenCodes distCodes tokens =
            Png.BitWriter.writeBits
              (Png.BitWriter.writeBits bw
                (dynamicPayloadTokenBits litLenCodes distCodes token)
                (dynamicPayloadTokenBitLen litLenCodes distCodes token))
              (dynamicPayloadStreamBits litLenCodes distCodes tokens)
              (dynamicPayloadStreamLen litLenCodes distCodes tokens) := by
        simpa [litLenCodes, distCodes] using htailWrite
      have hconcat :
          Png.BitWriter.writeBits bw
              (dynamicPayloadTokenBits litLenCodes distCodes token |||
                (dynamicPayloadStreamBits litLenCodes distCodes tokens <<<
                  dynamicPayloadTokenBitLen litLenCodes distCodes token))
              (dynamicPayloadTokenBitLen litLenCodes distCodes token +
                dynamicPayloadStreamLen litLenCodes distCodes tokens) =
            Png.BitWriter.writeBits
              (Png.BitWriter.writeBits bw
                (dynamicPayloadTokenBits litLenCodes distCodes token)
                (dynamicPayloadTokenBitLen litLenCodes distCodes token))
              (dynamicPayloadStreamBits litLenCodes distCodes tokens)
              (dynamicPayloadStreamLen litLenCodes distCodes tokens) :=
        Png.writeBits_concat bw
          (dynamicPayloadTokenBits litLenCodes distCodes token)
          (dynamicPayloadStreamBits litLenCodes distCodes tokens)
          (dynamicPayloadTokenBitLen litLenCodes distCodes token)
          (dynamicPayloadStreamLen litLenCodes distCodes tokens)
          htokenBits
      simp [writeDynamicPayloadTokensList, dynamicPayloadStreamBits,
        dynamicPayloadStreamLen, htokenWrite, htailWrite', hconcat]

/-- The generated source token array writes exactly its packed payload stream.
This is the array-shaped specialization used by the full dynamic encoder. -/
lemma writeDynamicPayloadTokensList_source_eq_writeBits
    (source : Array Png.DeflateToken)
    (hvalid : DeflateTokensMatchLengthsValid source)
    (bw : Png.BitWriter) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs source))
    writeDynamicPayloadTokensList bw litLenCodes distCodes source.toList =
      Png.BitWriter.writeBits bw
        (dynamicPayloadStreamBits litLenCodes distCodes source.toList)
        (dynamicPayloadStreamLen litLenCodes distCodes source.toList) := by
  exact writeDynamicPayloadTokensList_generated_eq_writeBits
    source source.toList hvalid
    (fun token hmem => deflateToken_mem_toList_index hmem) bw

/-- The generated payload EOB code produces a terminal dynamic-payload finish
step through the generic generated literal/length table. -/
lemma generatedDynamicPayloadEob_finish_readerAt_writeBits
    (source : Array Png.DeflateToken) (bw : Png.BitWriter)
    (out : ByteArray) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpec source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs source))
    let bits := dynamicPayloadEobBits litLenCodes
    let len := dynamicPayloadEobBitLen litLenCodes
    let bw' := Png.BitWriter.writeBits bw bits len
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bits len) hbit
    let br' := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bits len)
      bw'.flush
      (by
        simpa [bw'] using
          (le_rfl : (Png.BitWriter.writeBits bw bits len).flush.size ≤
            (Png.BitWriter.writeBits bw bits len).flush.size))
      (Png.bitPos_lt_8_writeBits bw bits len hbit)
    Png.DynamicPayloadFinish spec br0 out br' := by
  intro spec litLenCodes bits len bw' br0 br'
  have hlen : len = 9 := by
    simpa [len, litLenCodes] using
      dynamicPayloadEobBitLen_generated_eq_nine source
  have hdecode :
      (generatedDynamicLitLenTable source).decode br0 = some (256, br') := by
    have h :=
      generatedDynamicLitLenTable_decode_eob_readerAt_writeBits
        source bw 0 0 hbit hcur
    simpa [br0, br', bw', bits, len, litLenCodes, dynamicPayloadEobBits,
      hlen] using h
  exact Png.DynamicPayloadFinish.eob
    (spec := spec) (br := br0) (out := out)
    (sym := 256) (br' := br') (by simpa [spec] using hdecode)
    (by decide) (by decide)

/-- The empty generated payload-token list replays as a one-step trace that
only consumes the generated EOB marker. This is the base case for list traces. -/
lemma generatedDynamicPayloadTrace_nil_readerAt_writeBits
    (source : Array Png.DeflateToken) (bw : Png.BitWriter)
    (out : ByteArray) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpec source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs source))
    let bits := dynamicPayloadStreamBits litLenCodes distCodes []
    let len := dynamicPayloadStreamLen litLenCodes distCodes []
    let bw' := Png.BitWriter.writeBits bw bits len
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bits len) hbit
    let brAfter := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bits len)
      bw'.flush
      (by
        simpa [bw'] using
          (le_rfl : (Png.BitWriter.writeBits bw bits len).flush.size ≤
            (Png.BitWriter.writeBits bw bits len).flush.size))
      (Png.bitPos_lt_8_writeBits bw bits len hbit)
    Png.DynamicPayloadTrace spec 1 br0 out brAfter out := by
  intro spec litLenCodes distCodes bits len bw' br0 brAfter
  have hfinish :=
    generatedDynamicPayloadEob_finish_readerAt_writeBits
      (source := source) (bw := bw) (out := out) hbit hcur
  exact Png.DynamicPayloadTrace.finish
    (by
      simpa [spec, litLenCodes, distCodes, bits, len, bw', br0, brAfter,
        dynamicPayloadStreamBits, dynamicPayloadStreamLen] using hfinish)

/-- A generated literal payload token produces one validated dynamic-payload
literal transition through the generic generated literal/length table. -/
lemma generatedDynamicPayloadLiteral_transition_readerAt_writeBits
    (source : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (bw : Png.BitWriter) (out : ByteArray) (tailBits tailLen : Nat)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.DeflateToken.literal b)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpec source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs source))
    let bits := dynamicPayloadTokenBits litLenCodes distCodes
      (Png.DeflateToken.literal b)
    let len := dynamicPayloadTokenBitLen litLenCodes distCodes
      (Png.DeflateToken.literal b)
    let bitsTot := bits ||| (tailBits <<< len)
    let lenTot := len + tailLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br' := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot len)
      bw'.flush
      (by
        have hk : len ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot len lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot len hbit)
    Png.DynamicPayloadTransition spec br0 out br'
      (out.push (Png.u8 b.toNat)) := by
  intro spec litLenCodes distCodes bits len bitsTot lenTot bw' br0 br'
  have hlen : len = 9 := by
    simpa [len, litLenCodes, distCodes] using
      dynamicPayloadTokenBitLen_generated_literal_eq_nine_at
        source target b htarget ht
  have hdecode :
      (generatedDynamicLitLenTable source).decode br0 =
        some (b.toNat, br') := by
    have h :=
      generatedDynamicLitLenTable_decode_literal_at_readerAt_writeBits
        source target b bw tailBits tailLen htarget ht hbit hcur
    simpa [br0, br', bw', bits, len, bitsTot, lenTot, litLenCodes,
      distCodes, dynamicPayloadTokenBits, hlen] using h
  have hsym : b.toNat < 256 := UInt8.toNat_lt b
  exact Png.DynamicPayloadTransition.literal
    (spec := spec) (br := br0) (out := out)
    (sym := b.toNat) (br' := br') (by simpa [spec] using hdecode) hsym

/-- Builds a generic dynamic copy transition from already-proved match
decodes. This isolates the semantic `DynamicPayloadTransition.copy`
constructor from writer/reader arithmetic. -/
lemma dynamicPayloadTransition_copy_dist1_of_decodes
    (spec : Png.DynamicTableSpec) (br0 br1 br2 brAfter : Png.BitReader)
    (out out' : ByteArray) (matchLen : Nat)
    (hdecodeSym :
      spec.litLenTable.decode br0 =
        some ((Png.fixedLenMatchInfo matchLen).1, br1))
    (hdecodeLenEx :
      ∃ hsym hbits,
        Png.decodeLength (Png.fixedLenMatchInfo matchLen).1 br1
          hsym hbits = (matchLen, br2))
    (hdecodeDistEx :
      ∃ hdist hbitsD,
        spec.distTable.decode br2 = some (0, brAfter) ∧
        Png.decodeDistance 0 brAfter hdist hbitsD = (1, brAfter))
    (hcopy : Png.copyDistance out 1 matchLen = some out') :
    Png.DynamicPayloadTransition spec br0 out brAfter out' := by
  let sym := (Png.fixedLenMatchInfo matchLen).1
  rcases hdecodeLenEx with ⟨hsymLen, hbitsLen, hdecodeLen⟩
  rcases hdecodeDistEx with ⟨hdist0, hbitsD0, hdecodeDist, hdecodeDistance⟩
  let extra :=
    Png.lengthExtra[sym - 257]'(by
      have hidxle : sym - 257 ≤ 28 := by
        have hs := hsymLen
        omega
      have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
      have hsize : Png.lengthExtra.size = 29 := by decide
      simpa [hsize] using hidxlt)
  let extraD :=
    Png.distExtra[0]'(by
      have hDistExtraSize : Png.distExtra.size = 30 := by decide
      have hDistBasesSize : Png.distBases.size = 30 := by decide
      simpa [hDistExtraSize, hDistBasesSize] using hdist0)
  have hnotLit : ¬ sym < 256 := by
    have hs := hsymLen
    omega
  have hnotEob : (sym == 256) = false := by
    cases hbeq : (sym == 256) with
    | false => simpa using hbeq
    | true =>
        have hs : sym = 256 := by simpa [sym] using hbeq
        omega
  have hextra :
      extra =
        Array.getInternal Png.lengthExtra (sym - 257) (by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : Png.lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt) := by
    simp [extra, Array.getInternal, getElem!_pos]
  have hextraD :
      extraD =
        Array.getInternal Png.distExtra 0 (by
          have hDistExtraSize : Png.distExtra.size = 30 := by decide
          have hDistBasesSize : Png.distBases.size = 30 := by decide
          simpa [hDistExtraSize, hDistBasesSize] using hdist0) := by
    simp [extraD, Array.getInternal, getElem!_pos]
  exact Png.DynamicPayloadTransition.copy
    (spec := spec) (br := br0) (out := out)
    (sym := sym) (extra := extra) (len := matchLen)
    (distSym := 0) (extraD := extraD) (distance := 1)
    (br' := br1) (br'' := br2) (br''' := brAfter)
    (br'''' := brAfter) (out' := out')
    (by simpa [sym] using hdecodeSym)
    hnotLit hnotEob hsymLen hextra
    (by simpa [extra] using hbitsLen)
    (by simpa [sym] using hdecodeLen)
    hdecodeDist hdist0 hextraD
    (by simpa [extraD] using hbitsD0)
    (by simpa [extraD] using hdecodeDistance)
    hcopy

set_option maxRecDepth 200000 in
/-- After a generated match length symbol has decoded, the remaining generated
match payload decodes through the generic dynamic path as a distance-1 copy. -/
lemma generatedDynamicPayloadMatch_afterSym_transition_readerAt_writeBits
    (source : Array Png.DeflateToken) (target matchLen : Nat)
    (br0 : Png.BitReader) (bw1 : Png.BitWriter)
    (tailBits tailLen : Nat) (out : ByteArray)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.DeflateToken.matchDist1 matchLen)
    (hlen : 3 ≤ matchLen ∧ matchLen ≤ 258)
    (hout : 0 < out.size)
    (hbit1 : bw1.bitPos < 8) (hcur1 : bw1.curClearAbove) :
    let spec := generatedDynamicTableSpec source
    let info := Png.fixedLenMatchInfo matchLen
    let sym := info.1
    let extraBits := info.2.1
    let extraLen := info.2.2
    let distBitsTot := tailBits <<< 1
    let distLenTot := 1 + tailLen
    let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
    let lenLenTot := extraLen + distLenTot
    let bwLenAll := Png.BitWriter.writeBits bw1 lenBitsTot lenLenTot
    let br1 := Png.BitWriter.readerAt bw1 bwLenAll.flush
      (Png.flush_size_writeBits_le bw1 lenBitsTot lenLenTot) hbit1
    spec.litLenTable.decode br0 = some (sym, br1) →
      let bw2 := Png.BitWriter.writeBits bw1 lenBitsTot extraLen
      let bwDistAll := Png.BitWriter.writeBits bw2 distBitsTot distLenTot
      let brAfter := Png.BitWriter.readerAt
        (Png.BitWriter.writeBits bw2 distBitsTot 1) bwDistAll.flush
        (by
          have hk : 1 ≤ distLenTot := by omega
          simpa [distLenTot] using
            Png.flush_size_writeBits_prefix bw2 distBitsTot 1 distLenTot hk)
        (Png.bitPos_lt_8_writeBits bw2 distBitsTot 1
          (Png.bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1))
      Png.DynamicPayloadTransition spec br0 out brAfter
        (Png.pushRepeat out (out.get! (out.size - 1)) matchLen) := by
  intro spec info sym extraBits extraLen distBitsTot distLenTot lenBitsTot
    lenLenTot bwLenAll br1 hdecodeSym0 bw2 bwDistAll brAfter
  have hspecInternal :
      let info := Png.fixedLenMatchInfo matchLen
      let sym := info.1
      let extraBits := info.2.1
      let extraLen := info.2.2
      ∃ hsym : 257 ≤ sym ∧ sym ≤ 285,
        ∃ hidxBase : sym - 257 < Png.lengthBases.size,
          ∃ hidxExtra : sym - 257 < Png.lengthExtra.size,
            extraLen =
              Array.getInternal Png.lengthExtra (sym - 257) hidxExtra ∧
            Array.getInternal Png.lengthBases (sym - 257) hidxBase +
                extraBits = matchLen ∧
              extraBits < 2 ^ extraLen := by
    simpa [info, sym, extraBits, extraLen] using
      Png.fixedLenMatchInfo_spec_internal matchLen hlen.1 hlen.2
  rcases hspecInternal with ⟨_, _, _, _, _, hbitsLtExtra⟩
  have hmodLen : lenBitsTot % 2 ^ extraLen = extraBits := by
    have hmod' :=
      Png.mod_two_pow_or_shift extraBits distBitsTot extraLen extraLen le_rfl
    have hbitsMod : extraBits % 2 ^ extraLen = extraBits :=
      Nat.mod_eq_of_lt hbitsLtExtra
    simpa [lenBitsTot, hbitsMod] using hmod'
  have hwriteLenPrefix :
      Png.BitWriter.writeBits bw1 lenBitsTot extraLen =
        Png.BitWriter.writeBits bw1 extraBits extraLen := by
    calc
      Png.BitWriter.writeBits bw1 lenBitsTot extraLen =
          Png.BitWriter.writeBits bw1 (lenBitsTot % 2 ^ extraLen)
            extraLen := by
        simpa using Png.writeBits_mod bw1 lenBitsTot extraLen
      _ = Png.BitWriter.writeBits bw1 extraBits extraLen := by
        simp [hmodLen]
  have hconcatLen :
      Png.BitWriter.writeBits bw1 lenBitsTot lenLenTot =
        Png.BitWriter.writeBits bw2 distBitsTot distLenTot := by
    calc
      Png.BitWriter.writeBits bw1 lenBitsTot lenLenTot =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bw1 extraBits extraLen)
            distBitsTot distLenTot := by
        simpa [lenBitsTot, lenLenTot] using
          Png.writeBits_concat bw1 extraBits distBitsTot extraLen
            distLenTot hbitsLtExtra
      _ = Png.BitWriter.writeBits bw2 distBitsTot distLenTot := by
        simp [bw2, hwriteLenPrefix]
  let br2 := Png.BitWriter.readerAt bw2 bwLenAll.flush
    (by
      have hk : extraLen ≤ lenLenTot := by omega
      simpa [bwLenAll, lenLenTot] using
        Png.flush_size_writeBits_prefix bw1 lenBitsTot extraLen
          lenLenTot hk)
    (Png.bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1)
  have hdecodeLenEx' :=
    Png.decodeLength_fixedLenMatchInfo_readerAt_writeBits_prefix_exists
      (bw := bw1) (matchLen := matchLen) (restBits := distBitsTot)
      (restLen := distLenTot) (hlen := hlen) (hbit := hbit1)
      (hcur := hcur1)
  have hdecodeLenEx :
      ∃ hsym hbits0,
        Png.decodeLength sym br1 hsym hbits0 = (matchLen, br2) := by
    rcases hdecodeLenEx' with ⟨hsymLen, hbitsLen0, hdecodeLen0⟩
    have hdecodeLen0a :
        Png.decodeLength sym br1 hsymLen hbitsLen0 =
          (matchLen,
            Png.BitWriter.readerAt bw2 bwLenAll.flush
              (by
                have hk : extraLen ≤ lenLenTot := by omega
                simpa [bwLenAll, lenLenTot] using
                  Png.flush_size_writeBits_prefix bw1 lenBitsTot extraLen
                    lenLenTot hk)
              (Png.bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1)) := by
      simpa [sym, br1, bwLenAll, bw2] using hdecodeLen0
    refine ⟨hsymLen, hbitsLen0, ?_⟩
    simpa [br2] using hdecodeLen0a
  have hdistTriple :=
    generatedDynamicDistTable_decode_zero_distance_one_readerAt_writeBits
      (tokens := source) (target := target) (len := matchLen)
      (bw := bw2) (tailBits := tailBits) (tailLen := tailLen)
      htarget ht
      (Png.bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1)
      (Png.curClearAbove_writeBits bw1 lenBitsTot extraLen hbit1 hcur1)
  let br2Dist := Png.BitWriter.readerAt bw2 bwDistAll.flush
    (by
      have hk : extraLen ≤ lenLenTot := by omega
      simpa [bwDistAll, hconcatLen, lenLenTot] using
        Png.flush_size_writeBits_prefix bw1 lenBitsTot extraLen
          lenLenTot hk)
    (Png.bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1)
  have hbwEq : bwLenAll = bwDistAll := by
    simpa [bwLenAll, bwDistAll] using hconcatLen
  have hbr2Eq : br2 = br2Dist := by
    have hdata : br2.data = br2Dist.data := by
      simpa [br2, br2Dist, Png.BitWriter.readerAt] using
        congrArg Png.BitWriter.flush hbwEq
    have hbyte : br2.bytePos = br2Dist.bytePos := by
      simp [br2, br2Dist, Png.BitWriter.readerAt]
    have hbit : br2.bitPos = br2Dist.bitPos := by
      simp [br2, br2Dist, Png.BitWriter.readerAt]
    exact Png.BitReader.ext hdata hbyte hbit
  have hdecodeDistEx :
      ∃ hdist hbitsD0,
        (generatedDynamicDistTable source).decode br2 = some (0, brAfter) ∧
          Png.decodeDistance 0 brAfter hdist hbitsD0 = (1, brAfter) := by
    rcases hdistTriple with
      ⟨hdist0, hbitsD0, hdecodeDistSym0, hdecodeDist0⟩
    have hdecodeDistSym0' :
        (generatedDynamicDistTable source).decode br2Dist =
          some (0, brAfter) := by
      simpa [br2Dist, brAfter, bwDistAll, distLenTot, distBitsTot]
        using hdecodeDistSym0
    refine ⟨hdist0, hbitsD0, ?_, ?_⟩
    · simpa [hbr2Eq] using hdecodeDistSym0'
    · change Png.decodeDistance 0 brAfter hdist0 hbitsD0 = (1, brAfter)
      exact hdecodeDist0
  have hcopy :
      Png.copyDistance out 1 matchLen =
        some (Png.pushRepeat out (out.get! (out.size - 1)) matchLen) :=
    Png.copyDistance_one_eq_pushRepeat out matchLen hout
  simpa [spec, generatedDynamicTableSpec, info, sym, extraBits, extraLen,
    distBitsTot, distLenTot, lenBitsTot, lenLenTot, bwLenAll, br1, bw2,
    bwDistAll, br2, br2Dist, brAfter, hbwEq, hbr2Eq] using
    dynamicPayloadTransition_copy_dist1_of_decodes
      (spec := spec) (br0 := br0) (br1 := br1) (br2 := br2)
      (brAfter := brAfter) (out := out)
      (out' := Png.pushRepeat out (out.get! (out.size - 1)) matchLen)
      (matchLen := matchLen) (hdecodeSym := by simpa [spec] using hdecodeSym0)
      (hdecodeLenEx := hdecodeLenEx)
      (hdecodeDistEx := by simpa [spec, generatedDynamicTableSpec] using hdecodeDistEx)
      (hcopy := hcopy)

set_option maxRecDepth 200000 in
/-- A generated match token, written as its literal/length code followed by
length-extra bits and the generated distance-zero code, produces one generic
dynamic-payload distance-1 copy transition. -/
lemma generatedDynamicPayloadMatch_manual_transition_readerAt_writeBits
    (source : Array Png.DeflateToken) (target matchLen : Nat)
    (bw : Png.BitWriter) (tailBits tailLen : Nat) (out : ByteArray)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.DeflateToken.matchDist1 matchLen)
    (hlen : 3 ≤ matchLen ∧ matchLen ≤ 258)
    (hout : 0 < out.size)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpec source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs source))
    let info := Png.fixedLenMatchInfo matchLen
    let sym := info.1
    let extraBits := info.2.1
    let extraLen := info.2.2
    let distBitsTot := tailBits <<< 1
    let distLenTot := 1 + tailLen
    let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
    let lenLenTot := extraLen + distLenTot
    let litBits := litLenCodes[sym]!.1
    let bitsTot := litBits ||| (lenBitsTot <<< 9)
    let lenTot := 9 + lenLenTot
    let bwAll := Png.BitWriter.writeBits bw bitsTot lenTot
    let bwSym := Png.BitWriter.writeBits bw bitsTot 9
    let br0 := Png.BitWriter.readerAt bw bwAll.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let bw2 := Png.BitWriter.writeBits bwSym lenBitsTot extraLen
    let bwDistAll := Png.BitWriter.writeBits bw2 distBitsTot distLenTot
    let brAfter := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw2 distBitsTot 1) bwDistAll.flush
      (by
        have hk : 1 ≤ distLenTot := by omega
        simpa [distLenTot] using
          Png.flush_size_writeBits_prefix bw2 distBitsTot 1 distLenTot hk)
      (Png.bitPos_lt_8_writeBits bw2 distBitsTot 1
        (Png.bitPos_lt_8_writeBits bwSym lenBitsTot extraLen
          (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)))
    Png.DynamicPayloadTransition spec br0 out brAfter
      (Png.pushRepeat out (out.get! (out.size - 1)) matchLen) := by
  intro spec litLenCodes info sym extraBits extraLen distBitsTot distLenTot
    lenBitsTot lenLenTot litBits bitsTot lenTot bwAll bwSym br0 bw2
    bwDistAll brAfter
  let br1 := Png.BitWriter.readerAt bwSym bwAll.flush
    (by
      have hk : 9 ≤ lenTot := by omega
      simpa [bwSym, lenTot] using
        Png.flush_size_writeBits_prefix bw bitsTot 9 lenTot hk)
    (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
  have hlitBits : litBits < 2 ^ 9 := by
    have h :=
      generatedDynamicLitLenCodes_match_bits_lt_codeSpace_at
        source target matchLen htarget ht hlen
    simpa [litLenCodes, Png.generatedDynamicLitLenCodeLen, info, sym,
      extraBits, extraLen] using h
  have hwriteSymPrefix :
      bwSym = Png.BitWriter.writeBits bw litBits 9 := by
    simpa [bwSym, bitsTot] using
      Png.writeBits_or_shift_tail
        (bw := bw) (bits := litBits) (tailBits := lenBitsTot)
        (len := 9) hlitBits
  have hconcat :
      bwAll = Png.BitWriter.writeBits bwSym lenBitsTot lenLenTot := by
    have hconcatRaw :=
      Png.writeBits_concat bw litBits lenBitsTot 9 lenLenTot hlitBits
    simpa [bwAll, bitsTot, lenTot, bwSym, hwriteSymPrefix]
      using hconcatRaw
  have hdecodeSymRaw :=
    generatedDynamicLitLenTable_decode_match_at_readerAt_writeBits
      (tokens := source) (target := target) (len := matchLen)
      (bw := bw) (restBits := lenBitsTot) (restLen := lenLenTot)
      htarget ht hlen hbit hcur
  have hdecodeSym :
      spec.litLenTable.decode br0 = some (sym, br1) := by
    simpa [spec, generatedDynamicTableSpec, litLenCodes, info, sym,
      extraBits, extraLen, litBits, bitsTot, lenTot, bwAll, bwSym, br0,
      br1] using hdecodeSymRaw
  have hdecodeSymAfter :
      spec.litLenTable.decode br0 =
        some (sym,
          Png.BitWriter.readerAt bwSym
            (Png.BitWriter.writeBits bwSym lenBitsTot lenLenTot).flush
            (Png.flush_size_writeBits_le bwSym lenBitsTot lenLenTot)
            (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)) := by
    simpa [br1, hconcat] using hdecodeSym
  have hstep :=
    generatedDynamicPayloadMatch_afterSym_transition_readerAt_writeBits
      (source := source) (target := target) (matchLen := matchLen)
      (br0 := br0) (bw1 := bwSym) (tailBits := tailBits)
      (tailLen := tailLen) (out := out) htarget ht hlen hout
      (Png.bitPos_lt_8_writeBits bw bitsTot 9 hbit)
      (Png.curClearAbove_writeBits bw bitsTot 9 hbit hcur)
  simpa [spec, info, sym, extraBits, extraLen, distBitsTot, distLenTot,
    lenBitsTot, lenLenTot, bw2, bwDistAll, brAfter] using
    hstep hdecodeSymAfter

set_option maxRecDepth 200000 in
/-- Runtime-shaped generated match-token payload bits produce one generic
dynamic-payload distance-1 copy transition. This bridges the packed
`dynamicPayloadTokenBits` shape to the split replay lemma. -/
lemma generatedDynamicPayloadMatch_transition_readerAt_writeBits
    (source : Array Png.DeflateToken) (target matchLen : Nat)
    (bw : Png.BitWriter) (tailBits tailLen : Nat) (out : ByteArray)
    (htarget : target < source.size)
    (ht : source[target]'htarget = Png.DeflateToken.matchDist1 matchLen)
    (hlen : 3 ≤ matchLen ∧ matchLen ≤ 258)
    (hout : 0 < out.size)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpec source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs source))
    let bits :=
      dynamicPayloadTokenBits litLenCodes distCodes
        (Png.DeflateToken.matchDist1 matchLen)
    let bitLen :=
      dynamicPayloadTokenBitLen litLenCodes distCodes
        (Png.DeflateToken.matchDist1 matchLen)
    let bitsTot := bits ||| (tailBits <<< bitLen)
    let lenTot := bitLen + tailLen
    let bwAll := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bwAll.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let brAfter := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot bitLen) bwAll.flush
      (by
        have hk : bitLen ≤ lenTot := by omega
        simpa [lenTot] using
          Png.flush_size_writeBits_prefix bw bitsTot bitLen lenTot hk)
      (Png.bitPos_lt_8_writeBits bw bitsTot bitLen hbit)
    Png.DynamicPayloadTransition spec br0 out brAfter
      (Png.pushRepeat out (out.get! (out.size - 1)) matchLen) := by
  intro spec litLenCodes distCodes bits bitLen bitsTot lenTot bwAll br0
    brAfter
  let info := Png.fixedLenMatchInfo matchLen
  let sym := info.1
  let extraBits := info.2.1
  let extraLen := info.2.2
  let distBitsTot := tailBits <<< 1
  let distLenTot := 1 + tailLen
  let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
  let lenLenTot := extraLen + distLenTot
  let litBits := litLenCodes[sym]!.1
  let manualBitsTot := litBits ||| (lenBitsTot <<< 9)
  let manualLenTot := 9 + lenLenTot
  let bwManualAll := Png.BitWriter.writeBits bw manualBitsTot manualLenTot
  let bwManualSym := Png.BitWriter.writeBits bw manualBitsTot 9
  let bw2 := Png.BitWriter.writeBits bwManualSym lenBitsTot extraLen
  let bwDistAll := Png.BitWriter.writeBits bw2 distBitsTot distLenTot
  let brAfterSeq := Png.BitWriter.readerAt
    (Png.BitWriter.writeBits bw2 distBitsTot 1) bwDistAll.flush
    (by
      have hk : 1 ≤ distLenTot := by omega
      simpa [distLenTot] using
        Png.flush_size_writeBits_prefix bw2 distBitsTot 1 distLenTot hk)
    (Png.bitPos_lt_8_writeBits bw2 distBitsTot 1
      (Png.bitPos_lt_8_writeBits bwManualSym lenBitsTot extraLen
        (Png.bitPos_lt_8_writeBits bw manualBitsTot 9 hbit)))
  have hlitLen :
      litLenCodes[sym]!.2 = 9 := by
    simpa [litLenCodes, info, sym, extraBits, extraLen] using
      generatedDynamicLitLenCodes_match_len_eq_nine_at
        source target matchLen htarget ht hlen
  have hdistCode :
      distCodes[0]! = (0, 1) := by
    simpa [distCodes] using
      generatedDynamicDistCodes_zero_eq_of_match_at
        source target matchLen htarget ht
  have hbitLen : bitLen = 9 + extraLen + 1 := by
    simpa [bitLen, dynamicPayloadTokenBitLen, litLenCodes, distCodes, info,
      sym, extraBits, extraLen, hlitLen, hdistCode, Nat.add_assoc] using
      dynamicPayloadTokenBitLen_generated_match_eq
        source target matchLen htarget ht hlen
  have hbitsShape : bitsTot = manualBitsTot := by
    simp [bitsTot, bits, bitLen, manualBitsTot, litBits, lenBitsTot,
      distBitsTot, dynamicPayloadTokenBits, dynamicPayloadTokenBitLen,
      litLenCodes, distCodes, info, sym, extraBits, extraLen, hlitLen,
      hdistCode, hbitLen, Nat.or_assoc, Nat.shiftLeft_or_distrib,
      Png.shiftLeft_shiftLeft, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]
  have hlenShape : lenTot = manualLenTot := by
    simp [lenTot, bitLen, manualLenTot, lenLenTot, distLenTot, hbitLen,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hspecInternal :
      let info := Png.fixedLenMatchInfo matchLen
      let sym := info.1
      let extraBits := info.2.1
      let extraLen := info.2.2
      ∃ hsym : 257 ≤ sym ∧ sym ≤ 285,
        ∃ hidxBase : sym - 257 < Png.lengthBases.size,
          ∃ hidxExtra : sym - 257 < Png.lengthExtra.size,
            extraLen =
              Array.getInternal Png.lengthExtra (sym - 257) hidxExtra ∧
            Array.getInternal Png.lengthBases (sym - 257) hidxBase +
                extraBits = matchLen ∧
              extraBits < 2 ^ extraLen := by
    simpa [info, sym, extraBits, extraLen] using
      Png.fixedLenMatchInfo_spec_internal matchLen hlen.1 hlen.2
  rcases hspecInternal with ⟨_, _, _, _, _, hbitsLtExtra⟩
  have hlitBits : litBits < 2 ^ 9 := by
    have h :=
      generatedDynamicLitLenCodes_match_bits_lt_codeSpace_at
        source target matchLen htarget ht hlen
    simpa [litLenCodes, Png.generatedDynamicLitLenCodeLen, info, sym,
      extraBits, extraLen] using h
  have hwriteSymPrefix :
      bwManualSym = Png.BitWriter.writeBits bw litBits 9 := by
    simpa [bwManualSym, manualBitsTot] using
      Png.writeBits_or_shift_tail
        (bw := bw) (bits := litBits) (tailBits := lenBitsTot)
        (len := 9) hlitBits
  have hmodLen : lenBitsTot % 2 ^ extraLen = extraBits := by
    have hmod' :=
      Png.mod_two_pow_or_shift extraBits distBitsTot extraLen extraLen le_rfl
    have hbitsMod : extraBits % 2 ^ extraLen = extraBits :=
      Nat.mod_eq_of_lt hbitsLtExtra
    simpa [lenBitsTot, hbitsMod] using hmod'
  have hwriteLenPrefix :
      Png.BitWriter.writeBits bwManualSym lenBitsTot extraLen =
        Png.BitWriter.writeBits bwManualSym extraBits extraLen := by
    calc
      Png.BitWriter.writeBits bwManualSym lenBitsTot extraLen =
          Png.BitWriter.writeBits bwManualSym
            (lenBitsTot % 2 ^ extraLen) extraLen := by
        simpa using Png.writeBits_mod bwManualSym lenBitsTot extraLen
      _ = Png.BitWriter.writeBits bwManualSym extraBits extraLen := by
        simp [hmodLen]
  have hconcatFullSym :
      bwManualAll =
        Png.BitWriter.writeBits bwManualSym lenBitsTot lenLenTot := by
    have hconcatRaw :=
      Png.writeBits_concat bw litBits lenBitsTot 9 lenLenTot hlitBits
    simpa [bwManualAll, manualBitsTot, manualLenTot, bwManualSym,
      hwriteSymPrefix] using hconcatRaw
  have hconcatLenFull :
      Png.BitWriter.writeBits bwManualSym lenBitsTot lenLenTot =
        bwDistAll := by
    calc
      Png.BitWriter.writeBits bwManualSym lenBitsTot lenLenTot =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bwManualSym extraBits extraLen)
            distBitsTot distLenTot := by
        simpa [lenBitsTot, lenLenTot] using
          Png.writeBits_concat bwManualSym extraBits distBitsTot extraLen
            distLenTot hbitsLtExtra
      _ = bwDistAll := by
        simp [bw2, bwDistAll, hwriteLenPrefix]
  have hfullManual : bwManualAll = bwDistAll :=
    hconcatFullSym.trans hconcatLenFull
  have hwriterSym :
      Png.BitWriter.writeBits bw manualBitsTot (9 + (extraLen + 1)) =
        Png.BitWriter.writeBits bwManualSym lenBitsTot (extraLen + 1) := by
    have hconcatRaw :=
      Png.writeBits_concat bw litBits lenBitsTot 9 (extraLen + 1) hlitBits
    simpa [manualBitsTot, bwManualSym, hwriteSymPrefix] using hconcatRaw
  have hwriterLen :
      Png.BitWriter.writeBits bwManualSym lenBitsTot (extraLen + 1) =
        Png.BitWriter.writeBits bw2 distBitsTot 1 := by
    calc
      Png.BitWriter.writeBits bwManualSym lenBitsTot (extraLen + 1) =
          Png.BitWriter.writeBits
            (Png.BitWriter.writeBits bwManualSym extraBits extraLen)
            distBitsTot 1 := by
        simpa [lenBitsTot] using
          Png.writeBits_concat bwManualSym extraBits distBitsTot extraLen
            1 hbitsLtExtra
      _ = Png.BitWriter.writeBits bw2 distBitsTot 1 := by
        simp [bw2, hwriteLenPrefix]
  have hwriterPrefix :
      Png.BitWriter.writeBits bw2 distBitsTot 1 =
        Png.BitWriter.writeBits bw bitsTot bitLen := by
    calc
      Png.BitWriter.writeBits bw2 distBitsTot 1 =
          Png.BitWriter.writeBits bw manualBitsTot (9 + (extraLen + 1)) := by
        exact (hwriterSym.trans hwriterLen).symm
      _ = Png.BitWriter.writeBits bw bitsTot bitLen := by
        simp [hbitsShape, hbitLen, Nat.add_assoc]
  have hdataPrefix : bwDistAll.flush = bwAll.flush := by
    have hbw : bwAll = bwDistAll := by
      simpa [bwAll, bitsTot, lenTot, hbitsShape, hlenShape, bwManualAll,
        manualBitsTot, manualLenTot] using hfullManual
    simpa [hbw]
  have hbrAfterEq : brAfterSeq = brAfter := by
    refine readerAt_eq_of_eqs hwriterPrefix hdataPrefix _ _ _ _
  let br0Manual := Png.BitWriter.readerAt bw bwManualAll.flush
    (Png.flush_size_writeBits_le bw manualBitsTot manualLenTot) hbit
  have hdataStart : bwManualAll.flush = bwAll.flush := by
    rw [hfullManual]
    exact hdataPrefix
  have hbr0Eq : br0Manual = br0 := by
    refine readerAt_eq_of_eqs rfl hdataStart _ _ _ _
  have hmanual :=
    generatedDynamicPayloadMatch_manual_transition_readerAt_writeBits
      (source := source) (target := target) (matchLen := matchLen)
      (bw := bw) (tailBits := tailBits) (tailLen := tailLen) (out := out)
      htarget ht hlen hout hbit hcur
  have hmanualSeqManual :
      Png.DynamicPayloadTransition spec br0Manual out brAfterSeq
        (Png.pushRepeat out (out.get! (out.size - 1)) matchLen) := by
    simpa [spec, litLenCodes, info, sym, extraBits, extraLen, distBitsTot,
      distLenTot, lenBitsTot, lenLenTot, litBits, manualBitsTot,
      manualLenTot, bwManualAll, bwManualSym, br0Manual, bw2, bwDistAll,
      brAfterSeq] using hmanual
  have hmanualSeq :
      Png.DynamicPayloadTransition spec br0 out brAfterSeq
        (Png.pushRepeat out (out.get! (out.size - 1)) matchLen) := by
    simpa [hbr0Eq] using hmanualSeqManual
  simpa [hbrAfterEq] using hmanualSeq

/-- Re-normalizes the literal byte produced by generic dynamic decoding. This
lets generated payload traces use the original `UInt8` token byte directly. -/
@[simp] lemma u8_toNat_eq_self (b : UInt8) : Png.u8 b.toNat = b := by
  simp [Png.u8]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Replays a generated dynamic payload-token list through the generic
dynamic-Huffman payload trace. This is the recursive bridge from emitted
token bits to decoded output bytes. -/
lemma generatedDynamicPayloadTraceList_readerAt_writeBits
    (source : Array Png.DeflateToken) (tokens : List Png.DeflateToken)
    (hvalid : DeflateTokensMatchLengthsValid source)
    (hmember :
      ∀ token ∈ tokens, ∃ target, ∃ htarget : target < source.size,
        source[target]'htarget = token)
    (out : ByteArray)
    (houtValid : DynamicPayloadTraceOutputValid out tokens)
    (bw : Png.BitWriter)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let spec := generatedDynamicTableSpec source
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs source))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs source))
    let bits := dynamicPayloadStreamBits litLenCodes distCodes tokens
    let len := dynamicPayloadStreamLen litLenCodes distCodes tokens
    let bwAll := Png.BitWriter.writeBits bw bits len
    let br0 := Png.BitWriter.readerAt bw bwAll.flush
      (Png.flush_size_writeBits_le bw bits len) hbit
    let brAfter := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bits len)
      bwAll.flush
      (by
        simpa [bwAll] using
          (le_rfl : (Png.BitWriter.writeBits bw bits len).flush.size ≤
            (Png.BitWriter.writeBits bw bits len).flush.size))
      (Png.bitPos_lt_8_writeBits bw bits len hbit)
    Png.DynamicPayloadTrace spec (tokens.length + 1) br0 out brAfter
      (dynamicPayloadTraceOut out tokens) := by
  revert hmember out bw
  induction tokens with
  | nil =>
      intro _hmember out houtValid bw hbit hcur spec litLenCodes distCodes
        bits len bwAll br0 brAfter
      have htrace :=
        generatedDynamicPayloadTrace_nil_readerAt_writeBits
          (source := source) (bw := bw) (out := out) hbit hcur
      simpa [spec, litLenCodes, distCodes, bits, len, bwAll, br0, brAfter,
        dynamicPayloadStreamBits, dynamicPayloadStreamLen,
        dynamicPayloadTraceOut] using htrace
  | cons token tokens ih =>
      intro hmember out houtValid bw hbit hcur spec litLenCodes distCodes
        bits len bwAll br0 brAfter
      have htailMember :
          ∀ t ∈ tokens, ∃ target, ∃ htarget : target < source.size,
            source[target]'htarget = t := by
        intro t ht
        exact hmember t (List.mem_cons_of_mem token ht)
      let tokenBits := dynamicPayloadTokenBits litLenCodes distCodes token
      let tokenLen := dynamicPayloadTokenBitLen litLenCodes distCodes token
      let tailBits := dynamicPayloadStreamBits litLenCodes distCodes tokens
      let tailLen := dynamicPayloadStreamLen litLenCodes distCodes tokens
      let bwMid := Png.BitWriter.writeBits bw bits tokenLen
      let brMid := Png.BitWriter.readerAt bwMid bwAll.flush
        (by
          have hk : tokenLen ≤ len := by
            simp [len, dynamicPayloadStreamLen, tokenLen, tailLen]
          simpa [bwMid, bwAll] using
            Png.flush_size_writeBits_prefix bw bits tokenLen len hk)
        (Png.bitPos_lt_8_writeBits bw bits tokenLen hbit)
      have htokenBits :
          tokenBits < 2 ^ tokenLen := by
        cases token with
        | literal b =>
            rcases hmember (Png.DeflateToken.literal b) (by simp) with
              ⟨target, htarget, ht⟩
            simpa [litLenCodes, distCodes, tokenBits, tokenLen] using
              dynamicPayloadTokenBits_generated_literal_lt_codeSpace_at
                source target b htarget ht
        | matchDist1 matchLen =>
            rcases hmember (Png.DeflateToken.matchDist1 matchLen) (by simp) with
              ⟨target, htarget, ht⟩
            have hlen := hvalid target matchLen htarget ht
            simpa [litLenCodes, distCodes, tokenBits, tokenLen] using
              dynamicPayloadTokenBits_generated_match_lt_codeSpace_at
                source target matchLen htarget ht hlen
      have hprefix :
          bwMid = Png.BitWriter.writeBits bw tokenBits tokenLen := by
        simpa [bwMid, bits, dynamicPayloadStreamBits, tokenBits, tokenLen,
          tailBits] using
          Png.writeBits_or_shift_tail bw tokenBits tailBits tokenLen htokenBits
      let bwTailAll :=
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw tokenBits tokenLen) tailBits tailLen
      have hconcat :
          bwAll = bwTailAll := by
        have h :=
          Png.writeBits_concat bw tokenBits tailBits tokenLen tailLen htokenBits
        simpa [bwAll, bits, len, dynamicPayloadStreamBits,
          dynamicPayloadStreamLen, tokenBits, tokenLen, tailBits, tailLen,
          bwTailAll] using h
      have hbrMidEq :
          brMid =
            Png.BitWriter.readerAt
              (Png.BitWriter.writeBits bw tokenBits tokenLen)
              bwTailAll.flush
              (Png.flush_size_writeBits_le
                (Png.BitWriter.writeBits bw tokenBits tokenLen)
                tailBits tailLen)
              (Png.bitPos_lt_8_writeBits bw tokenBits tokenLen hbit) := by
        refine readerAt_eq_of_eqs hprefix ?_ _ _ _ _
        simpa [hconcat]
      have hbitMid :
          (Png.BitWriter.writeBits bw tokenBits tokenLen).bitPos < 8 :=
        Png.bitPos_lt_8_writeBits bw tokenBits tokenLen hbit
      have hcurMid :
          (Png.BitWriter.writeBits bw tokenBits tokenLen).curClearAbove :=
        Png.curClearAbove_writeBits bw tokenBits tokenLen hbit hcur
      cases token with
      | literal b =>
          rcases hmember (Png.DeflateToken.literal b) (by simp) with
            ⟨target, htarget, ht⟩
          have hstep :=
            generatedDynamicPayloadLiteral_transition_readerAt_writeBits
              (source := source) (target := target) (b := b) (bw := bw)
              (out := out) (tailBits := tailBits) (tailLen := tailLen)
              htarget ht hbit hcur
          have hstep' :
              Png.DynamicPayloadTransition spec br0 out brMid
                (out.push b) := by
            simpa [spec, litLenCodes, distCodes, tokenBits, tokenLen,
              tailBits, tailLen, bits, len, bwAll, br0, brMid,
              dynamicPayloadStreamBits, dynamicPayloadStreamLen] using hstep
          have htailValid :
              DynamicPayloadTraceOutputValid (out.push b) tokens := by
            simpa [DynamicPayloadTraceOutputValid] using houtValid
          have hrestRaw :=
            ih htailMember (out.push b)
              htailValid
              (Png.BitWriter.writeBits bw tokenBits tokenLen)
              hbitMid hcurMid
          have hrest :
              Png.DynamicPayloadTrace spec (tokens.length + 1) brMid
                (out.push b) brAfter
                (dynamicPayloadTraceOut (out.push b) tokens) := by
            have hbrAfterEq :
                Png.BitWriter.readerAt
                    (Png.BitWriter.writeBits
                      (Png.BitWriter.writeBits bw tokenBits tokenLen)
                      tailBits tailLen)
                    bwTailAll.flush
                    (by
                      simpa [bwTailAll] using
                        (le_rfl :
                          (Png.BitWriter.writeBits
                            (Png.BitWriter.writeBits bw tokenBits tokenLen)
                            tailBits tailLen).flush.size ≤
                          (Png.BitWriter.writeBits
                            (Png.BitWriter.writeBits bw tokenBits tokenLen)
                            tailBits tailLen).flush.size))
                    (Png.bitPos_lt_8_writeBits
                      (Png.BitWriter.writeBits bw tokenBits tokenLen)
                      tailBits tailLen hbitMid) = brAfter := by
              refine readerAt_eq_of_eqs ?_ ?_ _ _ _ _
              · simpa [bwAll, bwTailAll] using hconcat.symm
              · simpa [bwAll, bwTailAll] using
                  congrArg Png.BitWriter.flush hconcat.symm
            have hrest' := hrestRaw
            simpa [spec, litLenCodes, distCodes, tailBits, tailLen,
              bwTailAll, hbrMidEq, hbrAfterEq] using hrest'
          have htrace :=
            Png.DynamicPayloadTrace.step (spec := spec)
              (hstep := hstep') (hrest := hrest)
          simpa [dynamicPayloadTraceOut, Nat.add_assoc] using htrace
      | matchDist1 matchLen =>
          rcases hmember (Png.DeflateToken.matchDist1 matchLen) (by simp) with
            ⟨target, htarget, ht⟩
          have hlenMatch := hvalid target matchLen htarget ht
          have houtPos : 0 < out.size := by
            simpa [DynamicPayloadTraceOutputValid] using houtValid.1
          have hstep :=
            generatedDynamicPayloadMatch_transition_readerAt_writeBits
              (source := source) (target := target) (matchLen := matchLen)
              (bw := bw) (tailBits := tailBits) (tailLen := tailLen)
              (out := out) htarget ht hlenMatch houtPos hbit hcur
          let out' :=
            Png.pushRepeat out (out.get! (out.size - 1)) matchLen
          have hstep' :
              Png.DynamicPayloadTransition spec br0 out brMid out' := by
            simpa [spec, litLenCodes, distCodes, tokenBits, tokenLen,
              tailBits, tailLen, bits, len, bwAll, br0, brMid, out',
              dynamicPayloadStreamBits, dynamicPayloadStreamLen] using hstep
          have htailValid :
              DynamicPayloadTraceOutputValid out' tokens := by
            simpa [DynamicPayloadTraceOutputValid, out'] using houtValid.2
          have hrestRaw :=
            ih htailMember out'
              htailValid
              (Png.BitWriter.writeBits bw tokenBits tokenLen)
              hbitMid hcurMid
          have hrest :
              Png.DynamicPayloadTrace spec (tokens.length + 1) brMid
                out' brAfter (dynamicPayloadTraceOut out' tokens) := by
            have hbrAfterEq :
                Png.BitWriter.readerAt
                    (Png.BitWriter.writeBits
                      (Png.BitWriter.writeBits bw tokenBits tokenLen)
                      tailBits tailLen)
                    bwTailAll.flush
                    (by
                      simpa [bwTailAll] using
                        (le_rfl :
                          (Png.BitWriter.writeBits
                            (Png.BitWriter.writeBits bw tokenBits tokenLen)
                            tailBits tailLen).flush.size ≤
                          (Png.BitWriter.writeBits
                            (Png.BitWriter.writeBits bw tokenBits tokenLen)
                            tailBits tailLen).flush.size))
                    (Png.bitPos_lt_8_writeBits
                      (Png.BitWriter.writeBits bw tokenBits tokenLen)
                      tailBits tailLen hbitMid) = brAfter := by
              refine readerAt_eq_of_eqs ?_ ?_ _ _ _ _
              · simpa [bwAll, bwTailAll] using hconcat.symm
              · simpa [bwAll, bwTailAll] using
                  congrArg Png.BitWriter.flush hconcat.symm
            have hrest' := hrestRaw
            simpa [spec, litLenCodes, distCodes, tailBits, tailLen,
              bwTailAll, hbrMidEq, hbrAfterEq] using hrest'
          have htrace :=
            Png.DynamicPayloadTrace.step (spec := spec)
              (hstep := hstep') (hrest := hrest)
          simpa [dynamicPayloadTraceOut, out', Nat.add_assoc] using htrace

end Lemmas

end Bitmaps
