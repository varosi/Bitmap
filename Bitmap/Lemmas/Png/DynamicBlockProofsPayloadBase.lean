import Bitmap.Lemmas.Png.DynamicBlockProofsDecode
import Bitmap.Lemmas.Png.FixedBlockProofsCommon
import Bitmap.Lemmas.Png.FixedBlockProofsDecodeEob
import Bitmap.Lemmas.Png.FixedLiteral

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-! Base payload facts for the dynamic proof stack.

This module keeps the reusable Huffman and fixed-table facts separate from the
large fixed-literal decode cores so later files can build in parallel.
-/

/-- Identifies the 1-bit `readBits` case with `readBit`, which keeps later decode steps small. -/
lemma readBits_one_eq_readBit (br : BitReader)
    (h : br.bitIndex + 1 ≤ br.data.size * 8) :
    br.readBits 1 h = br.readBit := by
  rcases hbit : br.readBit with ⟨bit, br'⟩
  have hread' : br'.bitIndex + 0 ≤ br'.data.size * 8 := by
    simpa using bitIndex_le_dataBits br'
  have hsucc :=
    readBits_succ_eq (br := br) (k := 0) (h := h) (bit := bit) (br' := br') hbit hread'
  have hzero : br'.readBits 0 hread' = (0, br') := by
    have haux := readBits_eq_readBitsAux (br := br') (n := 0) (h := hread')
    simpa [BitReader.readBitsAux, BitReader.readBitsAuxAcc] using haux
  have hread1 : br.readBits 1 h = (bit, br') := by
    calc
    br.readBits 1 h = (bit ||| ((br'.readBits 0 hread').1 <<< 1), (br'.readBits 0 hread').2) := hsucc
    _ = (bit, br') := by rw [hzero]; simp
  exact hread1

/-- Unfolds one Huffman decode step when the selected table entry is empty. -/
lemma Huffman.decodeFuel_step_none
    (h : Huffman) (fuel code len : Nat) (br br' : BitReader) (bit : Nat)
    (hbyte : br.bytePos < br.data.size)
    (hread : br.readBit = (bit, br'))
    (htable : len + 1 < h.table.size)
    (hcode : code ||| (bit <<< len) < (Array.getInternal h.table (len + 1) htable).size)
    (hrow : Array.getInternal (Array.getInternal h.table (len + 1) htable)
      (code ||| (bit <<< len)) hcode = none) :
    Huffman.decodeFuel h (fuel + 1) code len br =
      Huffman.decodeFuel h fuel (code ||| (bit <<< len)) (len + 1) br' := by
  change
    (if br.bytePos < br.data.size then
      let (bit', br'') := br.readBit
      let code' := code ||| (bit' <<< len)
      let len' := len + 1
      if hlen : h.table.size ≤ len' then
        Huffman.decodeFuel h fuel code' len' br''
      else
        let row := Array.getInternal h.table len' (Nat.lt_of_not_ge hlen)
        if hcode' : code' < row.size then
          match Array.getInternal row code' hcode' with
          | some sym => some (sym, br'')
          | none => Huffman.decodeFuel h fuel code' len' br''
        else
          Huffman.decodeFuel h fuel code' len' br''
    else none) = _
  rw [if_pos hbyte, hread]
  simp only
  have hnotle : ¬ h.table.size ≤ len + 1 := Nat.not_le_of_lt htable
  by_cases hlen : h.table.size ≤ len + 1
  · exact False.elim (hnotle hlen)
  · simp [hlen]
    by_cases hcode' :
        code ||| (bit <<< len) <
          (Array.getInternal h.table (len + 1) (Nat.lt_of_not_ge hlen)).size
    ·
      have hrow' :
          Array.getInternal (Array.getInternal h.table (len + 1) (Nat.lt_of_not_ge hlen))
            (code ||| (bit <<< len)) hcode' = none := by
        simpa using hrow
      intro hcode''
      have hrow'' : h.table[len + 1][code ||| (bit <<< len)] = none := by
        simpa using hrow'
      rw [hrow'']
    · have hcode'' :
          code ||| (bit <<< len) <
            (Array.getInternal h.table (len + 1) (Nat.lt_of_not_ge hlen)).size := by
        simpa using hcode
      exact False.elim (hcode' hcode'')

/-- Unfolds one Huffman decode step when the selected table entry already resolves to a symbol. -/
lemma Huffman.decodeFuel_step_some
    (h : Huffman) (fuel code len : Nat) (br br' : BitReader) (bit sym : Nat)
    (hbyte : br.bytePos < br.data.size)
    (hread : br.readBit = (bit, br'))
    (htable : len + 1 < h.table.size)
    (hcode : code ||| (bit <<< len) < (Array.getInternal h.table (len + 1) htable).size)
    (hrow : Array.getInternal (Array.getInternal h.table (len + 1) htable)
      (code ||| (bit <<< len)) hcode = some sym) :
    Huffman.decodeFuel h (fuel + 1) code len br = some (sym, br') := by
  change
    (if br.bytePos < br.data.size then
      let (bit', br'') := br.readBit
      let code' := code ||| (bit' <<< len)
      let len' := len + 1
      if hlen : h.table.size ≤ len' then
        Huffman.decodeFuel h fuel code' len' br''
      else
        let row := Array.getInternal h.table len' (Nat.lt_of_not_ge hlen)
        if hcode' : code' < row.size then
          match Array.getInternal row code' hcode' with
          | some sym => some (sym, br'')
          | none => Huffman.decodeFuel h fuel code' len' br''
        else
          Huffman.decodeFuel h fuel code' len' br''
    else none) = _
  rw [if_pos hbyte, hread]
  simp only
  have hnotle : ¬ h.table.size ≤ len + 1 := Nat.not_le_of_lt htable
  by_cases hlen : h.table.size ≤ len + 1
  · exact False.elim (hnotle hlen)
  · simp [hlen]
    by_cases hcode' :
        code ||| (bit <<< len) <
          (Array.getInternal h.table (len + 1) (Nat.lt_of_not_ge hlen)).size
    ·
      have hrow' :
          Array.getInternal (Array.getInternal h.table (len + 1) (Nat.lt_of_not_ge hlen))
            (code ||| (bit <<< len)) hcode' = some sym := by
        simpa using hrow
      have hcode'' : code ||| (bit <<< len) < h.table[len + 1].size := by
        simpa using hcode'
      by_cases hcodeTable : code ||| (bit <<< len) < h.table[len + 1].size
      · have hrow'' : h.table[len + 1][code ||| (bit <<< len)] = some sym := by
          simpa using hrow'
        simp [hcodeTable, hrow'']
      · exact False.elim (hcodeTable hcode'')
    · have hcode'' :
          code ||| (bit <<< len) <
            (Array.getInternal h.table (len + 1) (Nat.lt_of_not_ge hlen)).size := by
        simpa using hcode
      exact False.elim (hcode' hcode'')

/-- Records the number of decode rows in the fixed literal/length Huffman table. -/
lemma fixedLitLenHuffman_table_size :
    fixedLitLenHuffman.table.size = 10 := by
  native_decide

/-- Shows that the short fixed rows are intentionally empty, so decode must continue deeper. -/
lemma fixedLitLenHuffman_small_row_get_none
    (len code : Nat)
    (hlen1 : 1 ≤ len) (hlen6 : len ≤ 6)
    (hcode : code <
      (Array.getInternal fixedLitLenHuffman.table len
        (by
          rw [fixedLitLenHuffman_table_size]
          omega)).size) :
    Array.getInternal
      (Array.getInternal fixedLitLenHuffman.table len
        (by
          rw [fixedLitLenHuffman_table_size]
          omega))
      code hcode = none := by
  have hcases : len = 1 ∨ len = 2 ∨ len = 3 ∨ len = 4 ∨ len = 5 ∨ len = 6 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [fixedLitLenHuffman] at hcode ⊢

/-- Picks out the end-of-block entry from the 7-bit fixed literal/length row. -/
lemma fixedLitLenHuffman_row7_get_eob :
    Array.getInternal
      (Array.getInternal fixedLitLenHuffman.table 7 (by native_decide))
      0 (by native_decide) = some 256 := by
  native_decide

set_option maxRecDepth 4000 in
/-- Rules out 7-bit row entries whose reversed prefix is already above the valid high-symbol range. -/
lemma fixedLitLenHuffman_row7_get_none_of_ge
    (bits : Nat)
    (hbits :
      bits <
        (Array.getInternal fixedLitLenHuffman.table 7
          (by native_decide : 7 < fixedLitLenHuffman.table.size)).size)
    (h24 : 24 ≤ reverseBits bits 7) :
    Array.getInternal
      (Array.getInternal fixedLitLenHuffman.table 7
        (by native_decide : 7 < fixedLitLenHuffman.table.size))
      bits hbits = none := by
  change fixedLitLenRow7[bits]'hbits = none
  exact fixedLitLenRow7_get_none_of_ge bits hbits h24

set_option maxRecDepth 4000 in
/-- Rules out 8-bit row entries whose reversed prefix is above the valid high-symbol range. -/
lemma fixedLitLenHuffman_row8_get_none_of_ge
    (bits : Nat)
    (hbits :
      bits <
        (Array.getInternal fixedLitLenHuffman.table 8
          (by native_decide : 8 < fixedLitLenHuffman.table.size)).size)
    (h200 : 200 ≤ reverseBits bits 8) :
    Array.getInternal
      (Array.getInternal fixedLitLenHuffman.table 8
        (by native_decide : 8 < fixedLitLenHuffman.table.size))
      bits hbits = none := by
  change fixedLitLenRow8[bits]'hbits = none
  exact fixedLitLenRow8_get_none_of_ge bits hbits h200

/-- Specializes the 8-bit row lookup to low literal symbols `0..143`. -/
lemma fixedLitLenHuffman_row8_get_lo
    (sym : Nat) (hsym : sym ≤ 143) :
    Array.getInternal
      (Array.getInternal fixedLitLenHuffman.table 8
        (by native_decide : 8 < fixedLitLenHuffman.table.size))
      (reverseBits (sym + 48) 8)
      (by
        simpa [fixedLitLenHuffman, fixedLitLenRow8_size, Nat.shiftLeft_eq] using
          (reverseBits_lt (sym + 48) 8)) = some sym := by
  simpa [fixedLitLenHuffman] using fixedLitLenCode_row_lo sym hsym

/-- Specializes the 9-bit row lookup to mid literal symbols `144..255`. -/
lemma fixedLitLenHuffman_row9_get_mid
    (sym : Nat) (h144 : 144 ≤ sym) (h255 : sym ≤ 255) :
    Array.getInternal
      (Array.getInternal fixedLitLenHuffman.table 9
        (by native_decide : 9 < fixedLitLenHuffman.table.size))
      (reverseBits (sym - 144 + 400) 9)
      (by
        simpa [fixedLitLenHuffman, fixedLitLenRow9_size, Nat.shiftLeft_eq] using
          (reverseBits_lt (sym - 144 + 400) 9)) = some sym := by
  simpa [fixedLitLenHuffman] using fixedLitLenCode_row_mid sym h144 h255

/-- Specializes the 7-bit row lookup to high symbols `256..279`, including EOB. -/
lemma fixedLitLenHuffman_row7_get_hi
    (sym : Nat) (h256 : 256 ≤ sym) (h279 : sym ≤ 279) :
    Array.getInternal
      (Array.getInternal fixedLitLenHuffman.table 7
        (by native_decide : 7 < fixedLitLenHuffman.table.size))
      (reverseBits (sym - 256) 7)
      (by
        simpa [fixedLitLenHuffman, fixedLitLenRow7_size, Nat.shiftLeft_eq] using
          (reverseBits_lt (sym - 256) 7)) = some sym := by
  simpa [fixedLitLenHuffman] using fixedLitLenCode_row_hi sym h256 h279

/-- Specializes the 8-bit row lookup to the final high-symbol range `280..287`. -/
lemma fixedLitLenHuffman_row8_get_hi2
    (sym : Nat) (h280 : 280 ≤ sym) (h287 : sym ≤ 287) :
    Array.getInternal
      (Array.getInternal fixedLitLenHuffman.table 8
        (by native_decide : 8 < fixedLitLenHuffman.table.size))
      (reverseBits (sym - 280 + 192) 8)
      (by
        simpa [fixedLitLenHuffman, fixedLitLenRow8_size, Nat.shiftLeft_eq] using
          (reverseBits_lt (sym - 280 + 192) 8)) = some sym := by
  simpa [fixedLitLenHuffman] using fixedLitLenCode_row_hi2 sym h280 h287

end Png

end Bitmaps
