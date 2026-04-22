import Bitmap.Lemmas.Png.DynamicBlockProofsReadTables
import Bitmap.Lemmas.Png.FixedBlockProofsCommon
import Bitmap.Lemmas.Png.FixedBlockProofsDecodeEob
import Bitmap.Lemmas.Png.FixedLiteral

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Core 8-bit fixed-table decoder proof used for low literals and the final high-symbol row. -/
lemma fixedLitLenHuffman_decode_readerAt_writeBits_len8_core
    (bw : BitWriter) (sym bitsTot restLen : Nat)
    (hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some none)
    (hrow8 : fixedLitLenRow8[bitsTot % 2 ^ 8]? = some (some sym))
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lenTot := 8 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br8 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 8) bw'.flush
      (by
        have hk : 8 ≤ lenTot := by omega
        simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 8 lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot 8 hbit)
    fixedLitLenHuffman.decode br0 = some (sym, br8) := by
  let lenTot := 8 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let bw1 := BitWriter.writeBits bw bitsTot 1
  let bw2 := BitWriter.writeBits bw bitsTot 2
  let bw3 := BitWriter.writeBits bw bitsTot 3
  let bw4 := BitWriter.writeBits bw bitsTot 4
  let bw5 := BitWriter.writeBits bw bitsTot 5
  let bw6 := BitWriter.writeBits bw bitsTot 6
  let bw7 := BitWriter.writeBits bw bitsTot 7
  let bw8 := BitWriter.writeBits bw bitsTot 8
  let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br1 := BitWriter.readerAt bw1 bw'.flush
    (by
      have hk : 1 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 1 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 1 hbit)
  let br2 := BitWriter.readerAt bw2 bw'.flush
    (by
      have hk : 2 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 2 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 2 hbit)
  let br3 := BitWriter.readerAt bw3 bw'.flush
    (by
      have hk : 3 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 3 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 3 hbit)
  let br4 := BitWriter.readerAt bw4 bw'.flush
    (by
      have hk : 4 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 4 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 4 hbit)
  let br5 := BitWriter.readerAt bw5 bw'.flush
    (by
      have hk : 5 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  let br6 := BitWriter.readerAt bw6 bw'.flush
    (by
      have hk : 6 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 6 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 6 hbit)
  let br7 := BitWriter.readerAt bw7 bw'.flush
    (by
      have hk : 7 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 7 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 7 hbit)
  let br8 := BitWriter.readerAt bw8 bw'.flush
    (by
      have hk : 8 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 8 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 8 hbit)
  have hbit1 : bw1.bitPos < 8 := by
    simpa [bw1] using (bitPos_lt_8_writeBits bw bitsTot 1 hbit)
  have hbit2 : bw2.bitPos < 8 := by
    simpa [bw2] using (bitPos_lt_8_writeBits bw bitsTot 2 hbit)
  have hbit3 : bw3.bitPos < 8 := by
    simpa [bw3] using (bitPos_lt_8_writeBits bw bitsTot 3 hbit)
  have hbit4 : bw4.bitPos < 8 := by
    simpa [bw4] using (bitPos_lt_8_writeBits bw bitsTot 4 hbit)
  have hbit5 : bw5.bitPos < 8 := by
    simpa [bw5] using (bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  have hbit6 : bw6.bitPos < 8 := by
    simpa [bw6] using (bitPos_lt_8_writeBits bw bitsTot 6 hbit)
  have hbit7 : bw7.bitPos < 8 := by
    simpa [bw7] using (bitPos_lt_8_writeBits bw bitsTot 7 hbit)
  have hcur1 : bw1.curClearAbove := by
    simpa [bw1] using (curClearAbove_writeBits bw bitsTot 1 hbit hcur)
  have hcur2 : bw2.curClearAbove := by
    simpa [bw2] using (curClearAbove_writeBits bw bitsTot 2 hbit hcur)
  have hcur3 : bw3.curClearAbove := by
    simpa [bw3] using (curClearAbove_writeBits bw bitsTot 3 hbit hcur)
  have hcur4 : bw4.curClearAbove := by
    simpa [bw4] using (curClearAbove_writeBits bw bitsTot 4 hbit hcur)
  have hcur5 : bw5.curClearAbove := by
    simpa [bw5] using (curClearAbove_writeBits bw bitsTot 5 hbit hcur)
  have hcur6 : bw6.curClearAbove := by
    simpa [bw6] using (curClearAbove_writeBits bw bitsTot 6 hbit hcur)
  have hcur7 : bw7.curClearAbove := by
    simpa [bw7] using (curClearAbove_writeBits bw bitsTot 7 hbit hcur)
  have hsplit1 : bw' = BitWriter.writeBits bw1 (bitsTot >>> 1) (lenTot - 1) := by
    have hk : 1 + (lenTot - 1) = lenTot := by omega
    simpa [bw', bw1, hk] using
      (writeBits_split bw bitsTot 1 (lenTot - 1))
  have hsplit2 : bw' = BitWriter.writeBits bw2 (bitsTot >>> 2) (lenTot - 2) := by
    have hk : 2 + (lenTot - 2) = lenTot := by omega
    simpa [bw', bw2, hk] using
      (writeBits_split bw bitsTot 2 (lenTot - 2))
  have hsplit3 : bw' = BitWriter.writeBits bw3 (bitsTot >>> 3) (lenTot - 3) := by
    have hk : 3 + (lenTot - 3) = lenTot := by omega
    simpa [bw', bw3, hk] using
      (writeBits_split bw bitsTot 3 (lenTot - 3))
  have hsplit4 : bw' = BitWriter.writeBits bw4 (bitsTot >>> 4) (lenTot - 4) := by
    have hk : 4 + (lenTot - 4) = lenTot := by omega
    simpa [bw', bw4, hk] using
      (writeBits_split bw bitsTot 4 (lenTot - 4))
  have hsplit5 : bw' = BitWriter.writeBits bw5 (bitsTot >>> 5) (lenTot - 5) := by
    have hk : 5 + (lenTot - 5) = lenTot := by omega
    simpa [bw', bw5, hk] using
      (writeBits_split bw bitsTot 5 (lenTot - 5))
  have hsplit6 : bw' = BitWriter.writeBits bw6 (bitsTot >>> 6) (lenTot - 6) := by
    have hk : 6 + (lenTot - 6) = lenTot := by omega
    simpa [bw', bw6, hk] using
      (writeBits_split bw bitsTot 6 (lenTot - 6))
  have hsplit7 : bw' = BitWriter.writeBits bw7 (bitsTot >>> 7) (lenTot - 7) := by
    have hk : 7 + (lenTot - 7) = lenTot := by omega
    simpa [bw', bw7, hk] using
      (writeBits_split bw bitsTot 7 (lenTot - 7))
  have hbound0 : br0.bitIndex + 1 ≤ br0.data.size * 8 := by
    simpa [br0, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 1)
        (by omega) hbit)
  have hbound1 : br1.bitIndex + 1 ≤ br1.data.size * 8 := by
    simpa [br1, bw', hsplit1, lenTot] using
      (readerAt_writeBits_bound (bw := bw1) (bits := bitsTot >>> 1) (len := lenTot - 1) (k := 1)
        (by omega) hbit1)
  have hbound2 : br2.bitIndex + 1 ≤ br2.data.size * 8 := by
    simpa [br2, bw', hsplit2, lenTot] using
      (readerAt_writeBits_bound (bw := bw2) (bits := bitsTot >>> 2) (len := lenTot - 2) (k := 1)
        (by omega) hbit2)
  have hbound3 : br3.bitIndex + 1 ≤ br3.data.size * 8 := by
    simpa [br3, bw', hsplit3, lenTot] using
      (readerAt_writeBits_bound (bw := bw3) (bits := bitsTot >>> 3) (len := lenTot - 3) (k := 1)
        (by omega) hbit3)
  have hbound4 : br4.bitIndex + 1 ≤ br4.data.size * 8 := by
    simpa [br4, bw', hsplit4, lenTot] using
      (readerAt_writeBits_bound (bw := bw4) (bits := bitsTot >>> 4) (len := lenTot - 4) (k := 1)
        (by omega) hbit4)
  have hbound5 : br5.bitIndex + 1 ≤ br5.data.size * 8 := by
    simpa [br5, bw', hsplit5, lenTot] using
      (readerAt_writeBits_bound (bw := bw5) (bits := bitsTot >>> 5) (len := lenTot - 5) (k := 1)
        (by omega) hbit5)
  have hbound6 : br6.bitIndex + 1 ≤ br6.data.size * 8 := by
    simpa [br6, bw', hsplit6, lenTot] using
      (readerAt_writeBits_bound (bw := bw6) (bits := bitsTot >>> 6) (len := lenTot - 6) (k := 1)
        (by omega) hbit6)
  have hbound7 : br7.bitIndex + 1 ≤ br7.data.size * 8 := by
    simpa [br7, bw', hsplit7, lenTot] using
      (readerAt_writeBits_bound (bw := bw7) (bits := bitsTot >>> 7) (len := lenTot - 7) (k := 1)
        (by omega) hbit7)
  have hbr0 : br0.bytePos < br0.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br0 (by omega)
  have hbr1 : br1.bytePos < br1.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br1 (by omega)
  have hbr2 : br2.bytePos < br2.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br2 (by omega)
  have hbr3 : br3.bytePos < br3.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br3 (by omega)
  have hbr4 : br4.bytePos < br4.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br4 (by omega)
  have hbr5 : br5.bytePos < br5.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br5 (by omega)
  have hbr6 : br6.bytePos < br6.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br6 (by omega)
  have hbr7 : br7.bytePos < br7.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br7 (by omega)
  have hread0 : br0.readBit = (bitsTot % 2, br1) := by
    simpa [br0, br1, bw', lenTot] using
      (readBit_readerAt_writeBits (bw := bw) (bits := bitsTot) (len := lenTot) hbit hcur (by omega))
  have hbw2 : BitWriter.writeBit bw1 ((bitsTot >>> 1) % 2) = bw2 := by
    simp [bw1, bw2, BitWriter.writeBits]
  have hread1 : br1.readBit = ((bitsTot >>> 1) % 2, br2) := by
    simpa [br1, br2, bw', hsplit1, hbw2, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw1) (bits := bitsTot >>> 1) (len := lenTot - 1) hbit1 hcur1 (by omega))
  have hshift2 : bitsTot >>> 1 >>> 1 = bitsTot >>> 2 := by
    simpa using (Nat.shiftRight_add bitsTot 1 1)
  have hbw3 : BitWriter.writeBit bw2 ((bitsTot >>> 2) % 2) = bw3 := by
    simp [bw2, bw3, BitWriter.writeBits, hshift2]
  have hread2 : br2.readBit = ((bitsTot >>> 2) % 2, br3) := by
    simpa [br2, br3, bw', hsplit2, hbw3, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw2) (bits := bitsTot >>> 2) (len := lenTot - 2) hbit2 hcur2 (by omega))
  have hshift3 : bitsTot >>> 1 >>> 1 >>> 1 = bitsTot >>> 3 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 = bitsTot >>> 2 >>> 1 := by simp [hshift2]
      _ = bitsTot >>> 3 := by simpa using (Nat.shiftRight_add bitsTot 2 1)
  have hbw4 : BitWriter.writeBit bw3 ((bitsTot >>> 3) % 2) = bw4 := by
    simp [bw3, bw4, BitWriter.writeBits, hshift3]
  have hread3 : br3.readBit = ((bitsTot >>> 3) % 2, br4) := by
    simpa [br3, br4, bw', hsplit3, hbw4, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw3) (bits := bitsTot >>> 3) (len := lenTot - 3) hbit3 hcur3 (by omega))
  have hshift4 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 4 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 3 >>> 1 := by simp [hshift3]
      _ = bitsTot >>> 4 := by simpa using (Nat.shiftRight_add bitsTot 3 1)
  have hbw5 : BitWriter.writeBit bw4 ((bitsTot >>> 4) % 2) = bw5 := by
    simp [bw4, bw5, BitWriter.writeBits, hshift4]
  have hread4 : br4.readBit = ((bitsTot >>> 4) % 2, br5) := by
    simpa [br4, br5, bw', hsplit4, hbw5, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw4) (bits := bitsTot >>> 4) (len := lenTot - 4) hbit4 hcur4 (by omega))
  have hshift5 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 5 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 4 >>> 1 := by simp [hshift4]
      _ = bitsTot >>> 5 := by simpa using (Nat.shiftRight_add bitsTot 4 1)
  have hbw6 : BitWriter.writeBit bw5 ((bitsTot >>> 5) % 2) = bw6 := by
    simp [bw5, bw6, BitWriter.writeBits, hshift5]
  have hread5 : br5.readBit = ((bitsTot >>> 5) % 2, br6) := by
    simpa [br5, br6, bw', hsplit5, hbw6, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw5) (bits := bitsTot >>> 5) (len := lenTot - 5) hbit5 hcur5 (by omega))
  have hshift6 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 6 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 5 >>> 1 := by simp [hshift5]
      _ = bitsTot >>> 6 := by simpa using (Nat.shiftRight_add bitsTot 5 1)
  have hbw7 : BitWriter.writeBit bw6 ((bitsTot >>> 6) % 2) = bw7 := by
    simp [bw6, bw7, BitWriter.writeBits, hshift6]
  have hread6 : br6.readBit = ((bitsTot >>> 6) % 2, br7) := by
    simpa [br6, br7, bw', hsplit6, hbw7, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw6) (bits := bitsTot >>> 6) (len := lenTot - 6) hbit6 hcur6 (by omega))
  have hshift7 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 7 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 6 >>> 1 := by
        simp [hshift6]
      _ = bitsTot >>> 7 := by simpa using (Nat.shiftRight_add bitsTot 6 1)
  have hbw8 : BitWriter.writeBit bw7 ((bitsTot >>> 7) % 2) = bw8 := by
    simp [bw7, bw8, BitWriter.writeBits, hshift7]
  have hread7 : br7.readBit = ((bitsTot >>> 7) % 2, br8) := by
    simpa [br7, br8, bw', hsplit7, hbw8, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw7) (bits := bitsTot >>> 7) (len := lenTot - 7) hbit7 hcur7 (by omega))
  have htable1 : 1 < fixedLitLenHuffman.table.size := by native_decide
  have htable2 : 2 < fixedLitLenHuffman.table.size := by native_decide
  have htable3 : 3 < fixedLitLenHuffman.table.size := by native_decide
  have htable4 : 4 < fixedLitLenHuffman.table.size := by native_decide
  have htable5 : 5 < fixedLitLenHuffman.table.size := by native_decide
  have htable6 : 6 < fixedLitLenHuffman.table.size := by native_decide
  have htable7 : 7 < fixedLitLenHuffman.table.size := by native_decide
  have htable8 : 8 < fixedLitLenHuffman.table.size := by native_decide
  have hcode1 : bitsTot % 2 <
      (Array.getInternal fixedLitLenHuffman.table 1 htable1).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 1))
  have hcode2 : bitsTot % 2 ^ 2 <
      (Array.getInternal fixedLitLenHuffman.table 2 htable2).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 2))
  have hcode3 : bitsTot % 2 ^ 3 <
      (Array.getInternal fixedLitLenHuffman.table 3 htable3).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 3))
  have hcode4 : bitsTot % 2 ^ 4 <
      (Array.getInternal fixedLitLenHuffman.table 4 htable4).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 4))
  have hcode5 : bitsTot % 2 ^ 5 <
      (Array.getInternal fixedLitLenHuffman.table 5 htable5).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 5))
  have hcode6 : bitsTot % 2 ^ 6 <
      (Array.getInternal fixedLitLenHuffman.table 6 htable6).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 6))
  have hcode7 : bitsTot % 2 ^ 7 <
      (Array.getInternal fixedLitLenHuffman.table 7 htable7).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 7))
  have hcode8 : bitsTot % 2 ^ 8 <
      (Array.getInternal fixedLitLenHuffman.table 8 htable8).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 8))
  have hrow1 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 1 htable1)
        (bitsTot % 2) hcode1 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 1) (code := bitsTot % 2)
      (by decide) (by decide) hcode1
  have hrow2 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 2 htable2)
        (bitsTot % 2 ^ 2) hcode2 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 2) (code := bitsTot % 2 ^ 2)
      (by decide) (by decide) hcode2
  have hrow3 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 3 htable3)
        (bitsTot % 2 ^ 3) hcode3 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 3) (code := bitsTot % 2 ^ 3)
      (by decide) (by decide) hcode3
  have hrow4 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 4 htable4)
        (bitsTot % 2 ^ 4) hcode4 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 4) (code := bitsTot % 2 ^ 4)
      (by decide) (by decide) hcode4
  have hrow5 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 5 htable5)
        (bitsTot % 2 ^ 5) hcode5 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 5) (code := bitsTot % 2 ^ 5)
      (by decide) (by decide) hcode5
  have hrow6 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 6 htable6)
        (bitsTot % 2 ^ 6) hcode6 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 6) (code := bitsTot % 2 ^ 6)
      (by decide) (by decide) hcode6
  have hrow7' :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 7 htable7)
        (bitsTot % 2 ^ 7) hcode7 = none := by
    have hrow7'' := hrow7
    rw [show fixedLitLenRow7[bitsTot % 2 ^ 7]? =
        some (fixedLitLenRow7[bitsTot % 2 ^ 7]'hcode7) by simp [hcode7]] at hrow7''
    exact Option.some.inj hrow7''
  have hrow8' :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 8 htable8)
        (bitsTot % 2 ^ 8) hcode8 = some sym := by
    have hrow8'' := hrow8
    rw [show fixedLitLenRow8[bitsTot % 2 ^ 8]? =
        some (fixedLitLenRow8[bitsTot % 2 ^ 8]'hcode8) by simp [hcode8]] at hrow8''
    exact Option.some.inj hrow8''
  have hprefix2 :
      bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1) = bitsTot % 2 ^ 2 := by
    simpa using (mod_two_pow_decomp_high bitsTot 1).symm
  have hprefix3 :
      bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2) = bitsTot % 2 ^ 3 := by
    simpa using (mod_two_pow_decomp_high bitsTot 2).symm
  have hprefix4 :
      bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3) = bitsTot % 2 ^ 4 := by
    simpa using (mod_two_pow_decomp_high bitsTot 3).symm
  have hprefix5 :
      bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4) = bitsTot % 2 ^ 5 := by
    simpa using (mod_two_pow_decomp_high bitsTot 4).symm
  have hprefix6 :
      bitsTot % 2 ^ 5 ||| (((bitsTot >>> 5) % 2) <<< 5) = bitsTot % 2 ^ 6 := by
    simpa using (mod_two_pow_decomp_high bitsTot 5).symm
  have hprefix7 :
      bitsTot % 2 ^ 6 ||| (((bitsTot >>> 6) % 2) <<< 6) = bitsTot % 2 ^ 7 := by
    simpa using (mod_two_pow_decomp_high bitsTot 6).symm
  have hprefix8 :
      bitsTot % 2 ^ 7 ||| (((bitsTot >>> 7) % 2) <<< 7) = bitsTot % 2 ^ 8 := by
    simpa using (mod_two_pow_decomp_high bitsTot 7).symm
  have hstep0 :
      fixedLitLenHuffman.decode br0 =
        Huffman.decodeFuel fixedLitLenHuffman 8 (bitsTot % 2) 1 br1 := by
    have hcode1' :
        0 ||| ((bitsTot % 2) <<< 0) <
          (Array.getInternal fixedLitLenHuffman.table 1 htable1).size := by
      simpa using hcode1
    have hrow1' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 1 htable1)
          (0 ||| ((bitsTot % 2) <<< 0)) hcode1' = none := by
      simpa using hrow1
    unfold Huffman.decode
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 8) (code := 0) (len := 0)
        (br := br0) (br' := br1) (bit := bitsTot % 2)
        (hbyte := hbr0) (hread := hread0) (htable := htable1) (hcode := hcode1')
        (hrow := hrow1'))
  have hstep1 :
      Huffman.decodeFuel fixedLitLenHuffman 8 (bitsTot % 2) 1 br1 =
        Huffman.decodeFuel fixedLitLenHuffman 7 (bitsTot % 2 ^ 2) 2 br2 := by
    have hcode' :
        bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1) <
          (Array.getInternal fixedLitLenHuffman.table 2 htable2).size := by
      simpa [hprefix2] using hcode2
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 2 htable2)
          (bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1)) hcode' = none := by
      simpa [hprefix2] using hrow2
    simpa [hprefix2] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 7) (code := bitsTot % 2)
        (len := 1) (br := br1) (br' := br2) (bit := (bitsTot >>> 1) % 2)
        (hbyte := hbr1) (hread := hread1) (htable := htable2) (hcode := hcode') (hrow := hrow''))
  have hstep2 :
      Huffman.decodeFuel fixedLitLenHuffman 7 (bitsTot % 2 ^ 2) 2 br2 =
        Huffman.decodeFuel fixedLitLenHuffman 6 (bitsTot % 2 ^ 3) 3 br3 := by
    have hcode' :
        bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2) <
          (Array.getInternal fixedLitLenHuffman.table 3 htable3).size := by
      simpa [hprefix3] using hcode3
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 3 htable3)
          (bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2)) hcode' = none := by
      simpa [hprefix3] using hrow3
    simpa [hprefix3] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 6) (code := bitsTot % 2 ^ 2)
        (len := 2) (br := br2) (br' := br3) (bit := (bitsTot >>> 2) % 2)
        (hbyte := hbr2) (hread := hread2) (htable := htable3) (hcode := hcode') (hrow := hrow''))
  have hstep3 :
      Huffman.decodeFuel fixedLitLenHuffman 6 (bitsTot % 2 ^ 3) 3 br3 =
        Huffman.decodeFuel fixedLitLenHuffman 5 (bitsTot % 2 ^ 4) 4 br4 := by
    have hcode' :
        bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3) <
          (Array.getInternal fixedLitLenHuffman.table 4 htable4).size := by
      simpa [hprefix4] using hcode4
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 4 htable4)
          (bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3)) hcode' = none := by
      simpa [hprefix4] using hrow4
    simpa [hprefix4] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 5) (code := bitsTot % 2 ^ 3)
        (len := 3) (br := br3) (br' := br4) (bit := (bitsTot >>> 3) % 2)
        (hbyte := hbr3) (hread := hread3) (htable := htable4) (hcode := hcode') (hrow := hrow''))
  have hstep4 :
      Huffman.decodeFuel fixedLitLenHuffman 5 (bitsTot % 2 ^ 4) 4 br4 =
        Huffman.decodeFuel fixedLitLenHuffman 4 (bitsTot % 2 ^ 5) 5 br5 := by
    have hcode' :
        bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4) <
          (Array.getInternal fixedLitLenHuffman.table 5 htable5).size := by
      simpa [hprefix5] using hcode5
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 5 htable5)
          (bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4)) hcode' = none := by
      simpa [hprefix5] using hrow5
    simpa [hprefix5] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 4) (code := bitsTot % 2 ^ 4)
        (len := 4) (br := br4) (br' := br5) (bit := (bitsTot >>> 4) % 2)
        (hbyte := hbr4) (hread := hread4) (htable := htable5) (hcode := hcode') (hrow := hrow''))
  have hstep5 :
      Huffman.decodeFuel fixedLitLenHuffman 4 (bitsTot % 2 ^ 5) 5 br5 =
        Huffman.decodeFuel fixedLitLenHuffman 3 (bitsTot % 2 ^ 6) 6 br6 := by
    have hcode' :
        bitsTot % 2 ^ 5 ||| (((bitsTot >>> 5) % 2) <<< 5) <
          (Array.getInternal fixedLitLenHuffman.table 6 htable6).size := by
      simpa [hprefix6] using hcode6
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 6 htable6)
          (bitsTot % 2 ^ 5 ||| (((bitsTot >>> 5) % 2) <<< 5)) hcode' = none := by
      simpa [hprefix6] using hrow6
    simpa [hprefix6] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 3) (code := bitsTot % 2 ^ 5)
        (len := 5) (br := br5) (br' := br6) (bit := (bitsTot >>> 5) % 2)
        (hbyte := hbr5) (hread := hread5) (htable := htable6) (hcode := hcode') (hrow := hrow''))
  have hstep6 :
      Huffman.decodeFuel fixedLitLenHuffman 3 (bitsTot % 2 ^ 6) 6 br6 =
        Huffman.decodeFuel fixedLitLenHuffman 2 (bitsTot % 2 ^ 7) 7 br7 := by
    have hcode' :
        bitsTot % 2 ^ 6 ||| (((bitsTot >>> 6) % 2) <<< 6) <
          (Array.getInternal fixedLitLenHuffman.table 7 htable7).size := by
      simpa [hprefix7] using hcode7
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 7 htable7)
          (bitsTot % 2 ^ 6 ||| (((bitsTot >>> 6) % 2) <<< 6)) hcode' = none := by
      simpa [hprefix7] using hrow7'
    simpa [hprefix7] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 2) (code := bitsTot % 2 ^ 6)
        (len := 6) (br := br6) (br' := br7) (bit := (bitsTot >>> 6) % 2)
        (hbyte := hbr6) (hread := hread6) (htable := htable7) (hcode := hcode') (hrow := hrow''))
  have hstep7 :
      Huffman.decodeFuel fixedLitLenHuffman 2 (bitsTot % 2 ^ 7) 7 br7 = some (sym, br8) := by
    have hcode' :
        bitsTot % 2 ^ 7 ||| (((bitsTot >>> 7) % 2) <<< 7) <
          (Array.getInternal fixedLitLenHuffman.table 8 htable8).size := by
      simpa [hprefix8] using hcode8
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 8 htable8)
          (bitsTot % 2 ^ 7 ||| (((bitsTot >>> 7) % 2) <<< 7)) hcode' = some sym := by
      simpa [hprefix8] using hrow8'
    simpa [hprefix8] using
      (Huffman.decodeFuel_step_some (h := fixedLitLenHuffman) (fuel := 1) (code := bitsTot % 2 ^ 7)
        (len := 7) (br := br7) (br' := br8) (bit := (bitsTot >>> 7) % 2) (sym := sym)
        (hbyte := hbr7) (hread := hread7) (htable := htable8) (hcode := hcode') (hrow := hrow''))
  calc
    fixedLitLenHuffman.decode br0 = Huffman.decodeFuel fixedLitLenHuffman 8 (bitsTot % 2) 1 br1 := hstep0
    _ = Huffman.decodeFuel fixedLitLenHuffman 7 (bitsTot % 2 ^ 2) 2 br2 := hstep1
    _ = Huffman.decodeFuel fixedLitLenHuffman 6 (bitsTot % 2 ^ 3) 3 br3 := hstep2
    _ = Huffman.decodeFuel fixedLitLenHuffman 5 (bitsTot % 2 ^ 4) 4 br4 := hstep3
    _ = Huffman.decodeFuel fixedLitLenHuffman 4 (bitsTot % 2 ^ 5) 5 br5 := hstep4
    _ = Huffman.decodeFuel fixedLitLenHuffman 3 (bitsTot % 2 ^ 6) 6 br6 := hstep5
    _ = Huffman.decodeFuel fixedLitLenHuffman 2 (bitsTot % 2 ^ 7) 7 br7 := hstep6
    _ = some (sym, br8) := hstep7

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Core 9-bit fixed-table decoder proof used for the middle literal range. -/
lemma fixedLitLenHuffman_decode_readerAt_writeBits_len9_core
    (bw : BitWriter) (sym bitsTot restLen : Nat)
    (hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some none)
    (hrow8 : fixedLitLenRow8[bitsTot % 2 ^ 8]? = some none)
    (hrow9 : fixedLitLenRow9[bitsTot % 2 ^ 9]? = some (some sym))
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lenTot := 9 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br9 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 9) bw'.flush
      (by
        have hk : 9 ≤ lenTot := by omega
        simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot 9 hbit)
    fixedLitLenHuffman.decode br0 = some (sym, br9) := by
  let lenTot := 9 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let bw1 := BitWriter.writeBits bw bitsTot 1
  let bw2 := BitWriter.writeBits bw bitsTot 2
  let bw3 := BitWriter.writeBits bw bitsTot 3
  let bw4 := BitWriter.writeBits bw bitsTot 4
  let bw5 := BitWriter.writeBits bw bitsTot 5
  let bw6 := BitWriter.writeBits bw bitsTot 6
  let bw7 := BitWriter.writeBits bw bitsTot 7
  let bw8 := BitWriter.writeBits bw bitsTot 8
  let bw9 := BitWriter.writeBits bw bitsTot 9
  let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br1 := BitWriter.readerAt bw1 bw'.flush
    (by
      have hk : 1 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 1 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 1 hbit)
  let br2 := BitWriter.readerAt bw2 bw'.flush
    (by
      have hk : 2 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 2 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 2 hbit)
  let br3 := BitWriter.readerAt bw3 bw'.flush
    (by
      have hk : 3 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 3 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 3 hbit)
  let br4 := BitWriter.readerAt bw4 bw'.flush
    (by
      have hk : 4 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 4 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 4 hbit)
  let br5 := BitWriter.readerAt bw5 bw'.flush
    (by
      have hk : 5 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  let br6 := BitWriter.readerAt bw6 bw'.flush
    (by
      have hk : 6 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 6 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 6 hbit)
  let br7 := BitWriter.readerAt bw7 bw'.flush
    (by
      have hk : 7 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 7 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 7 hbit)
  let br8 := BitWriter.readerAt bw8 bw'.flush
    (by
      have hk : 8 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 8 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 8 hbit)
  let br9 := BitWriter.readerAt bw9 bw'.flush
    (by
      have hk : 9 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 9 hbit)
  have hbit1 : bw1.bitPos < 8 := by
    simpa [bw1] using (bitPos_lt_8_writeBits bw bitsTot 1 hbit)
  have hbit2 : bw2.bitPos < 8 := by
    simpa [bw2] using (bitPos_lt_8_writeBits bw bitsTot 2 hbit)
  have hbit3 : bw3.bitPos < 8 := by
    simpa [bw3] using (bitPos_lt_8_writeBits bw bitsTot 3 hbit)
  have hbit4 : bw4.bitPos < 8 := by
    simpa [bw4] using (bitPos_lt_8_writeBits bw bitsTot 4 hbit)
  have hbit5 : bw5.bitPos < 8 := by
    simpa [bw5] using (bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  have hbit6 : bw6.bitPos < 8 := by
    simpa [bw6] using (bitPos_lt_8_writeBits bw bitsTot 6 hbit)
  have hbit7 : bw7.bitPos < 8 := by
    simpa [bw7] using (bitPos_lt_8_writeBits bw bitsTot 7 hbit)
  have hbit8 : bw8.bitPos < 8 := by
    simpa [bw8] using (bitPos_lt_8_writeBits bw bitsTot 8 hbit)
  have hcur1 : bw1.curClearAbove := by
    simpa [bw1] using (curClearAbove_writeBits bw bitsTot 1 hbit hcur)
  have hcur2 : bw2.curClearAbove := by
    simpa [bw2] using (curClearAbove_writeBits bw bitsTot 2 hbit hcur)
  have hcur3 : bw3.curClearAbove := by
    simpa [bw3] using (curClearAbove_writeBits bw bitsTot 3 hbit hcur)
  have hcur4 : bw4.curClearAbove := by
    simpa [bw4] using (curClearAbove_writeBits bw bitsTot 4 hbit hcur)
  have hcur5 : bw5.curClearAbove := by
    simpa [bw5] using (curClearAbove_writeBits bw bitsTot 5 hbit hcur)
  have hcur6 : bw6.curClearAbove := by
    simpa [bw6] using (curClearAbove_writeBits bw bitsTot 6 hbit hcur)
  have hcur7 : bw7.curClearAbove := by
    simpa [bw7] using (curClearAbove_writeBits bw bitsTot 7 hbit hcur)
  have hcur8 : bw8.curClearAbove := by
    simpa [bw8] using (curClearAbove_writeBits bw bitsTot 8 hbit hcur)
  have hsplit1 : bw' = BitWriter.writeBits bw1 (bitsTot >>> 1) (lenTot - 1) := by
    have hk : 1 + (lenTot - 1) = lenTot := by omega
    simpa [bw', bw1, hk] using
      (writeBits_split bw bitsTot 1 (lenTot - 1))
  have hsplit2 : bw' = BitWriter.writeBits bw2 (bitsTot >>> 2) (lenTot - 2) := by
    have hk : 2 + (lenTot - 2) = lenTot := by omega
    simpa [bw', bw2, hk] using
      (writeBits_split bw bitsTot 2 (lenTot - 2))
  have hsplit3 : bw' = BitWriter.writeBits bw3 (bitsTot >>> 3) (lenTot - 3) := by
    have hk : 3 + (lenTot - 3) = lenTot := by omega
    simpa [bw', bw3, hk] using
      (writeBits_split bw bitsTot 3 (lenTot - 3))
  have hsplit4 : bw' = BitWriter.writeBits bw4 (bitsTot >>> 4) (lenTot - 4) := by
    have hk : 4 + (lenTot - 4) = lenTot := by omega
    simpa [bw', bw4, hk] using
      (writeBits_split bw bitsTot 4 (lenTot - 4))
  have hsplit5 : bw' = BitWriter.writeBits bw5 (bitsTot >>> 5) (lenTot - 5) := by
    have hk : 5 + (lenTot - 5) = lenTot := by omega
    simpa [bw', bw5, hk] using
      (writeBits_split bw bitsTot 5 (lenTot - 5))
  have hsplit6 : bw' = BitWriter.writeBits bw6 (bitsTot >>> 6) (lenTot - 6) := by
    have hk : 6 + (lenTot - 6) = lenTot := by omega
    simpa [bw', bw6, hk] using
      (writeBits_split bw bitsTot 6 (lenTot - 6))
  have hsplit7 : bw' = BitWriter.writeBits bw7 (bitsTot >>> 7) (lenTot - 7) := by
    have hk : 7 + (lenTot - 7) = lenTot := by omega
    simpa [bw', bw7, hk] using
      (writeBits_split bw bitsTot 7 (lenTot - 7))
  have hsplit8 : bw' = BitWriter.writeBits bw8 (bitsTot >>> 8) (lenTot - 8) := by
    have hk : 8 + (lenTot - 8) = lenTot := by omega
    simpa [bw', bw8, hk] using
      (writeBits_split bw bitsTot 8 (lenTot - 8))
  have hbound0 : br0.bitIndex + 1 ≤ br0.data.size * 8 := by
    simpa [br0, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 1)
        (by omega) hbit)
  have hbound1 : br1.bitIndex + 1 ≤ br1.data.size * 8 := by
    simpa [br1, bw', hsplit1, lenTot] using
      (readerAt_writeBits_bound (bw := bw1) (bits := bitsTot >>> 1) (len := lenTot - 1) (k := 1)
        (by omega) hbit1)
  have hbound2 : br2.bitIndex + 1 ≤ br2.data.size * 8 := by
    simpa [br2, bw', hsplit2, lenTot] using
      (readerAt_writeBits_bound (bw := bw2) (bits := bitsTot >>> 2) (len := lenTot - 2) (k := 1)
        (by omega) hbit2)
  have hbound3 : br3.bitIndex + 1 ≤ br3.data.size * 8 := by
    simpa [br3, bw', hsplit3, lenTot] using
      (readerAt_writeBits_bound (bw := bw3) (bits := bitsTot >>> 3) (len := lenTot - 3) (k := 1)
        (by omega) hbit3)
  have hbound4 : br4.bitIndex + 1 ≤ br4.data.size * 8 := by
    simpa [br4, bw', hsplit4, lenTot] using
      (readerAt_writeBits_bound (bw := bw4) (bits := bitsTot >>> 4) (len := lenTot - 4) (k := 1)
        (by omega) hbit4)
  have hbound5 : br5.bitIndex + 1 ≤ br5.data.size * 8 := by
    simpa [br5, bw', hsplit5, lenTot] using
      (readerAt_writeBits_bound (bw := bw5) (bits := bitsTot >>> 5) (len := lenTot - 5) (k := 1)
        (by omega) hbit5)
  have hbound6 : br6.bitIndex + 1 ≤ br6.data.size * 8 := by
    simpa [br6, bw', hsplit6, lenTot] using
      (readerAt_writeBits_bound (bw := bw6) (bits := bitsTot >>> 6) (len := lenTot - 6) (k := 1)
        (by omega) hbit6)
  have hbound7 : br7.bitIndex + 1 ≤ br7.data.size * 8 := by
    simpa [br7, bw', hsplit7, lenTot] using
      (readerAt_writeBits_bound (bw := bw7) (bits := bitsTot >>> 7) (len := lenTot - 7) (k := 1)
        (by omega) hbit7)
  have hbound8 : br8.bitIndex + 1 ≤ br8.data.size * 8 := by
    simpa [br8, bw', hsplit8, lenTot] using
      (readerAt_writeBits_bound (bw := bw8) (bits := bitsTot >>> 8) (len := lenTot - 8) (k := 1)
        (by omega) hbit8)
  have hread0 : br0.readBit = (bitsTot % 2, br1) := by
    simpa [br0, br1, bw', lenTot] using
      (readBit_readerAt_writeBits (bw := bw) (bits := bitsTot) (len := lenTot) hbit hcur (by omega))
  have hbw2 : BitWriter.writeBit bw1 ((bitsTot >>> 1) % 2) = bw2 := by
    simp [bw1, bw2, BitWriter.writeBits]
  have hread1 : br1.readBit = ((bitsTot >>> 1) % 2, br2) := by
    simpa [br1, br2, bw', hsplit1, hbw2, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw1) (bits := bitsTot >>> 1) (len := lenTot - 1) hbit1 hcur1 (by omega))
  have hshift2 : bitsTot >>> 1 >>> 1 = bitsTot >>> 2 := by
    simpa using (Nat.shiftRight_add bitsTot 1 1)
  have hbw3 : BitWriter.writeBit bw2 ((bitsTot >>> 2) % 2) = bw3 := by
    simp [bw2, bw3, BitWriter.writeBits, hshift2]
  have hread2 : br2.readBit = ((bitsTot >>> 2) % 2, br3) := by
    simpa [br2, br3, bw', hsplit2, hbw3, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw2) (bits := bitsTot >>> 2) (len := lenTot - 2) hbit2 hcur2 (by omega))
  have hshift3 : bitsTot >>> 1 >>> 1 >>> 1 = bitsTot >>> 3 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 = bitsTot >>> 2 >>> 1 := by simp [hshift2]
      _ = bitsTot >>> 3 := by simpa using (Nat.shiftRight_add bitsTot 2 1)
  have hbw4 : BitWriter.writeBit bw3 ((bitsTot >>> 3) % 2) = bw4 := by
    simp [bw3, bw4, BitWriter.writeBits, hshift3]
  have hread3 : br3.readBit = ((bitsTot >>> 3) % 2, br4) := by
    simpa [br3, br4, bw', hsplit3, hbw4, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw3) (bits := bitsTot >>> 3) (len := lenTot - 3) hbit3 hcur3 (by omega))
  have hshift4 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 4 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 3 >>> 1 := by simp [hshift3]
      _ = bitsTot >>> 4 := by simpa using (Nat.shiftRight_add bitsTot 3 1)
  have hbw5 : BitWriter.writeBit bw4 ((bitsTot >>> 4) % 2) = bw5 := by
    simp [bw4, bw5, BitWriter.writeBits, hshift4]
  have hread4 : br4.readBit = ((bitsTot >>> 4) % 2, br5) := by
    simpa [br4, br5, bw', hsplit4, hbw5, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw4) (bits := bitsTot >>> 4) (len := lenTot - 4) hbit4 hcur4 (by omega))
  have hshift5 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 5 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 4 >>> 1 := by simp [hshift4]
      _ = bitsTot >>> 5 := by simpa using (Nat.shiftRight_add bitsTot 4 1)
  have hbw6 : BitWriter.writeBit bw5 ((bitsTot >>> 5) % 2) = bw6 := by
    simp [bw5, bw6, BitWriter.writeBits, hshift5]
  have hread5 : br5.readBit = ((bitsTot >>> 5) % 2, br6) := by
    simpa [br5, br6, bw', hsplit5, hbw6, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw5) (bits := bitsTot >>> 5) (len := lenTot - 5) hbit5 hcur5 (by omega))
  have hshift6 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 6 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 5 >>> 1 := by simp [hshift5]
      _ = bitsTot >>> 6 := by simpa using (Nat.shiftRight_add bitsTot 5 1)
  have hbw7 : BitWriter.writeBit bw6 ((bitsTot >>> 6) % 2) = bw7 := by
    simp [bw6, bw7, BitWriter.writeBits, hshift6]
  have hread6 : br6.readBit = ((bitsTot >>> 6) % 2, br7) := by
    simpa [br6, br7, bw', hsplit6, hbw7, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw6) (bits := bitsTot >>> 6) (len := lenTot - 6) hbit6 hcur6 (by omega))
  have hshift7 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 7 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 6 >>> 1 := by
        simp [hshift6]
      _ = bitsTot >>> 7 := by simpa using (Nat.shiftRight_add bitsTot 6 1)
  have hbw8 : BitWriter.writeBit bw7 ((bitsTot >>> 7) % 2) = bw8 := by
    simp [bw7, bw8, BitWriter.writeBits, hshift7]
  have hread7 : br7.readBit = ((bitsTot >>> 7) % 2, br8) := by
    simpa [br7, br8, bw', hsplit7, hbw8, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw7) (bits := bitsTot >>> 7) (len := lenTot - 7) hbit7 hcur7 (by omega))
  have hshift8 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 8 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 7 >>> 1 := by
        simp [hshift7]
      _ = bitsTot >>> 8 := by simpa using (Nat.shiftRight_add bitsTot 7 1)
  have hbw9 : BitWriter.writeBit bw8 ((bitsTot >>> 8) % 2) = bw9 := by
    simp [bw8, bw9, BitWriter.writeBits, hshift8]
  have hread8 : br8.readBit = ((bitsTot >>> 8) % 2, br9) := by
    simpa [br8, br9, bw', hsplit8, hbw9, lenTot] using
      (readBit_readerAt_writeBits
        (bw := bw8) (bits := bitsTot >>> 8) (len := lenTot - 8) hbit8 hcur8 (by omega))
  have hprefix9 :
      bitsTot % 2 ^ 8 ||| (((bitsTot >>> 8) % 2) <<< 8) = bitsTot % 2 ^ 9 := by
    simpa using (mod_two_pow_decomp_high bitsTot 8).symm
  have htable1 : 1 < fixedLitLenHuffman.table.size := by native_decide
  have htable2 : 2 < fixedLitLenHuffman.table.size := by native_decide
  have htable3 : 3 < fixedLitLenHuffman.table.size := by native_decide
  have htable4 : 4 < fixedLitLenHuffman.table.size := by native_decide
  have htable5 : 5 < fixedLitLenHuffman.table.size := by native_decide
  have htable6 : 6 < fixedLitLenHuffman.table.size := by native_decide
  have htable7 : 7 < fixedLitLenHuffman.table.size := by native_decide
  have htable8 : 8 < fixedLitLenHuffman.table.size := by native_decide
  have htable9 : 9 < fixedLitLenHuffman.table.size := by native_decide
  have hcode1 : bitsTot % 2 <
      (Array.getInternal fixedLitLenHuffman.table 1 htable1).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 1))
  have hcode2 : bitsTot % 2 ^ 2 <
      (Array.getInternal fixedLitLenHuffman.table 2 htable2).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 2))
  have hcode3 : bitsTot % 2 ^ 3 <
      (Array.getInternal fixedLitLenHuffman.table 3 htable3).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 3))
  have hcode4 : bitsTot % 2 ^ 4 <
      (Array.getInternal fixedLitLenHuffman.table 4 htable4).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 4))
  have hcode5 : bitsTot % 2 ^ 5 <
      (Array.getInternal fixedLitLenHuffman.table 5 htable5).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 5))
  have hcode6 : bitsTot % 2 ^ 6 <
      (Array.getInternal fixedLitLenHuffman.table 6 htable6).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 6))
  have hcode7 : bitsTot % 2 ^ 7 <
      (Array.getInternal fixedLitLenHuffman.table 7 htable7).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 7))
  have hcode8 : bitsTot % 2 ^ 8 <
      (Array.getInternal fixedLitLenHuffman.table 8 htable8).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 8))
  have hcode9 : bitsTot % 2 ^ 9 <
      (Array.getInternal fixedLitLenHuffman.table 9 htable9).size := by
    simpa [fixedLitLenHuffman, Nat.shiftLeft_eq] using
      (Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 9))
  have hrow1 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 1 htable1)
        (bitsTot % 2) hcode1 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 1) (code := bitsTot % 2)
      (by decide) (by decide) hcode1
  have hrow2 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 2 htable2)
        (bitsTot % 2 ^ 2) hcode2 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 2) (code := bitsTot % 2 ^ 2)
      (by decide) (by decide) hcode2
  have hrow3 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 3 htable3)
        (bitsTot % 2 ^ 3) hcode3 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 3) (code := bitsTot % 2 ^ 3)
      (by decide) (by decide) hcode3
  have hrow4 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 4 htable4)
        (bitsTot % 2 ^ 4) hcode4 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 4) (code := bitsTot % 2 ^ 4)
      (by decide) (by decide) hcode4
  have hrow5 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 5 htable5)
        (bitsTot % 2 ^ 5) hcode5 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 5) (code := bitsTot % 2 ^ 5)
      (by decide) (by decide) hcode5
  have hrow6 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 6 htable6)
        (bitsTot % 2 ^ 6) hcode6 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 6) (code := bitsTot % 2 ^ 6)
      (by decide) (by decide) hcode6
  have hrow7' :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 7 htable7)
        (bitsTot % 2 ^ 7) hcode7 = none := by
    have hrow7'' := hrow7
    rw [show fixedLitLenRow7[bitsTot % 2 ^ 7]? =
        some (fixedLitLenRow7[bitsTot % 2 ^ 7]'hcode7) by simp [hcode7]] at hrow7''
    exact Option.some.inj hrow7''
  have hrow8' :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 8 htable8)
        (bitsTot % 2 ^ 8) hcode8 = none := by
    have hrow8'' := hrow8
    rw [show fixedLitLenRow8[bitsTot % 2 ^ 8]? =
        some (fixedLitLenRow8[bitsTot % 2 ^ 8]'hcode8) by simp [hcode8]] at hrow8''
    exact Option.some.inj hrow8''
  have hrow9' :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 9 htable9)
        (bitsTot % 2 ^ 9) hcode9 = some sym := by
    have hrow9'' := hrow9
    rw [show fixedLitLenRow9[bitsTot % 2 ^ 9]? =
        some (fixedLitLenRow9[bitsTot % 2 ^ 9]'hcode9) by simp [hcode9]] at hrow9''
    exact Option.some.inj hrow9''
  have hbr0 : br0.bytePos < br0.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br0 (by omega)
  have hbr7 : br7.bytePos < br7.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br7 (by omega)
  have hbr8 : br8.bytePos < br8.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br8 (by omega)
  have hprefix2 :
      bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1) = bitsTot % 2 ^ 2 := by
    simpa using (mod_two_pow_decomp_high bitsTot 1).symm
  have hprefix3 :
      bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2) = bitsTot % 2 ^ 3 := by
    simpa using (mod_two_pow_decomp_high bitsTot 2).symm
  have hprefix4 :
      bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3) = bitsTot % 2 ^ 4 := by
    simpa using (mod_two_pow_decomp_high bitsTot 3).symm
  have hprefix5 :
      bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4) = bitsTot % 2 ^ 5 := by
    simpa using (mod_two_pow_decomp_high bitsTot 4).symm
  have hprefix6 :
      bitsTot % 2 ^ 5 ||| (((bitsTot >>> 5) % 2) <<< 5) = bitsTot % 2 ^ 6 := by
    simpa using (mod_two_pow_decomp_high bitsTot 5).symm
  have hprefix7 :
      bitsTot % 2 ^ 6 ||| (((bitsTot >>> 6) % 2) <<< 6) = bitsTot % 2 ^ 7 := by
    simpa using (mod_two_pow_decomp_high bitsTot 6).symm
  have hprefix8 :
      bitsTot % 2 ^ 7 ||| (((bitsTot >>> 7) % 2) <<< 7) = bitsTot % 2 ^ 8 := by
    simpa using (mod_two_pow_decomp_high bitsTot 7).symm
  have hstep0 :
      fixedLitLenHuffman.decode br0 =
        Huffman.decodeFuel fixedLitLenHuffman 8 (bitsTot % 2) 1 br1 := by
    have hcode1' :
        0 ||| ((bitsTot % 2) <<< 0) <
          (Array.getInternal fixedLitLenHuffman.table 1 htable1).size := by
      simpa using hcode1
    have hrow1' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 1 htable1)
          (0 ||| ((bitsTot % 2) <<< 0)) hcode1' = none := by
      simpa using hrow1
    unfold Huffman.decode
    simpa [hread0] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 8) (code := 0) (len := 0)
        (br := br0) (br' := br1) (bit := bitsTot % 2)
        (hbyte := hbr0) (hread := hread0) (htable := htable1) (hcode := hcode1')
        (hrow := hrow1'))
  have hstep1 :
      Huffman.decodeFuel fixedLitLenHuffman 8 (bitsTot % 2) 1 br1 =
        Huffman.decodeFuel fixedLitLenHuffman 7 (bitsTot % 2 ^ 2) 2 br2 := by
    have hcode' :
        bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1) <
          (Array.getInternal fixedLitLenHuffman.table 2 htable2).size := by
      simpa [hprefix2] using hcode2
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 2 htable2)
          (bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1)) hcode' = none := by
      simpa [hprefix2] using hrow2
    simpa [hread0, hread1, hprefix2] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 7) (code := bitsTot % 2)
        (len := 1) (br := br1) (br' := br2) (bit := (bitsTot >>> 1) % 2)
        (hbyte := bytePos_lt_of_bitIndex_lt_dataBits br1 (by omega)) (hread := hread1)
        (htable := htable2) (hcode := hcode') (hrow := hrow''))
  have hstep2 :
      Huffman.decodeFuel fixedLitLenHuffman 7 (bitsTot % 2 ^ 2) 2 br2 =
        Huffman.decodeFuel fixedLitLenHuffman 6 (bitsTot % 2 ^ 3) 3 br3 := by
    have hcode' :
        bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2) <
          (Array.getInternal fixedLitLenHuffman.table 3 htable3).size := by
      simpa [hprefix3] using hcode3
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 3 htable3)
          (bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2)) hcode' = none := by
      simpa [hprefix3] using hrow3
    have hbr2 : br2.bytePos < br2.data.size := by
      exact bytePos_lt_of_bitIndex_lt_dataBits br2 (by omega)
    simpa [hprefix3] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 6) (code := bitsTot % 2 ^ 2)
        (len := 2) (br := br2) (br' := br3) (bit := (bitsTot >>> 2) % 2)
        (hbyte := hbr2) (hread := hread2) (htable := htable3) (hcode := hcode') (hrow := hrow''))
  have hstep3 :
      Huffman.decodeFuel fixedLitLenHuffman 6 (bitsTot % 2 ^ 3) 3 br3 =
        Huffman.decodeFuel fixedLitLenHuffman 5 (bitsTot % 2 ^ 4) 4 br4 := by
    have hcode' :
        bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3) <
          (Array.getInternal fixedLitLenHuffman.table 4 htable4).size := by
      simpa [hprefix4] using hcode4
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 4 htable4)
          (bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3)) hcode' = none := by
      simpa [hprefix4] using hrow4
    have hbr3 : br3.bytePos < br3.data.size := by
      exact bytePos_lt_of_bitIndex_lt_dataBits br3 (by omega)
    have hread3' : br3.readBit = ((bitsTot >>> 3) % 2, br4) := by
      simpa using hread3
    simpa [hprefix4] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 5) (code := bitsTot % 2 ^ 3)
        (len := 3) (br := br3) (br' := br4) (bit := (bitsTot >>> 3) % 2)
        (hbyte := hbr3) (hread := hread3') (htable := htable4) (hcode := hcode') (hrow := hrow''))
  have hstep4 :
      Huffman.decodeFuel fixedLitLenHuffman 5 (bitsTot % 2 ^ 4) 4 br4 =
        Huffman.decodeFuel fixedLitLenHuffman 4 (bitsTot % 2 ^ 5) 5 br5 := by
    have hcode' :
        bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4) <
          (Array.getInternal fixedLitLenHuffman.table 5 htable5).size := by
      simpa [hprefix5] using hcode5
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 5 htable5)
          (bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4)) hcode' = none := by
      simpa [hprefix5] using hrow5
    have hbr4 : br4.bytePos < br4.data.size := by
      exact bytePos_lt_of_bitIndex_lt_dataBits br4 (by omega)
    have hread4' : br4.readBit = ((bitsTot >>> 4) % 2, br5) := by
      simpa using hread4
    simpa [hprefix5] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 4) (code := bitsTot % 2 ^ 4)
        (len := 4) (br := br4) (br' := br5) (bit := (bitsTot >>> 4) % 2)
        (hbyte := hbr4) (hread := hread4') (htable := htable5) (hcode := hcode') (hrow := hrow''))
  have hstep5 :
      Huffman.decodeFuel fixedLitLenHuffman 4 (bitsTot % 2 ^ 5) 5 br5 =
        Huffman.decodeFuel fixedLitLenHuffman 3 (bitsTot % 2 ^ 6) 6 br6 := by
    have hcode' :
        bitsTot % 2 ^ 5 ||| (((bitsTot >>> 5) % 2) <<< 5) <
          (Array.getInternal fixedLitLenHuffman.table 6 htable6).size := by
      simpa [hprefix6] using hcode6
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 6 htable6)
          (bitsTot % 2 ^ 5 ||| (((bitsTot >>> 5) % 2) <<< 5)) hcode' = none := by
      simpa [hprefix6] using hrow6
    have hbr5 : br5.bytePos < br5.data.size := by
      exact bytePos_lt_of_bitIndex_lt_dataBits br5 (by omega)
    have hread5' : br5.readBit = ((bitsTot >>> 5) % 2, br6) := by
      simpa using hread5
    simpa [hprefix6] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 3) (code := bitsTot % 2 ^ 5)
        (len := 5) (br := br5) (br' := br6) (bit := (bitsTot >>> 5) % 2)
        (hbyte := hbr5) (hread := hread5') (htable := htable6) (hcode := hcode') (hrow := hrow''))
  have hstep6 :
      Huffman.decodeFuel fixedLitLenHuffman 3 (bitsTot % 2 ^ 6) 6 br6 =
        Huffman.decodeFuel fixedLitLenHuffman 2 (bitsTot % 2 ^ 7) 7 br7 := by
    have hcode' :
        bitsTot % 2 ^ 6 ||| (((bitsTot >>> 6) % 2) <<< 6) <
          (Array.getInternal fixedLitLenHuffman.table 7 htable7).size := by
      simpa [hprefix7] using hcode7
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 7 htable7)
          (bitsTot % 2 ^ 6 ||| (((bitsTot >>> 6) % 2) <<< 6)) hcode' = none := by
      simpa [hprefix7] using hrow7'
    have hbr6 : br6.bytePos < br6.data.size := by
      exact bytePos_lt_of_bitIndex_lt_dataBits br6 (by omega)
    have hread6' : br6.readBit = ((bitsTot >>> 6) % 2, br7) := by
      simpa using hread6
    simpa [hprefix7] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 2) (code := bitsTot % 2 ^ 6)
        (len := 6) (br := br6) (br' := br7) (bit := (bitsTot >>> 6) % 2)
        (hbyte := hbr6) (hread := hread6') (htable := htable7) (hcode := hcode') (hrow := hrow''))
  have hstep7 :
      Huffman.decodeFuel fixedLitLenHuffman 2 (bitsTot % 2 ^ 7) 7 br7 =
        Huffman.decodeFuel fixedLitLenHuffman 1 (bitsTot % 2 ^ 8) 8 br8 := by
    have hcode' :
        bitsTot % 2 ^ 7 ||| (((bitsTot >>> 7) % 2) <<< 7) <
          (Array.getInternal fixedLitLenHuffman.table 8 htable8).size := by
      simpa [hprefix8] using hcode8
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 8 htable8)
          (bitsTot % 2 ^ 7 ||| (((bitsTot >>> 7) % 2) <<< 7)) hcode' = none := by
      simpa [hprefix8] using hrow8'
    simpa [hprefix8] using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 1) (code := bitsTot % 2 ^ 7)
        (len := 7) (br := br7) (br' := br8) (bit := (bitsTot >>> 7) % 2)
        (hbyte := hbr7) (hread := hread7) (htable := htable8) (hcode := hcode') (hrow := hrow''))
  have hstep8 :
      Huffman.decodeFuel fixedLitLenHuffman 1 (bitsTot % 2 ^ 8) 8 br8 = some (sym, br9) := by
    have hcode' :
        bitsTot % 2 ^ 8 ||| (((bitsTot >>> 8) % 2) <<< 8) <
          (Array.getInternal fixedLitLenHuffman.table 9 htable9).size := by
      simpa [hprefix9] using hcode9
    have hrow'' :
        Array.getInternal (Array.getInternal fixedLitLenHuffman.table 9 htable9)
          (bitsTot % 2 ^ 8 ||| (((bitsTot >>> 8) % 2) <<< 8)) hcode' = some sym := by
      simpa [hprefix9] using hrow9'
    simpa [hprefix9] using
      (Huffman.decodeFuel_step_some (h := fixedLitLenHuffman) (fuel := 0) (code := bitsTot % 2 ^ 8)
        (len := 8) (br := br8) (br' := br9) (bit := (bitsTot >>> 8) % 2) (sym := sym)
        (hbyte := hbr8) (hread := hread8) (htable := htable9) (hcode := hcode') (hrow := hrow''))
  calc
    fixedLitLenHuffman.decode br0 = Huffman.decodeFuel fixedLitLenHuffman 8 (bitsTot % 2) 1 br1 := by
      simpa [br1, hread0] using hstep0
    _ = Huffman.decodeFuel fixedLitLenHuffman 7 (bitsTot % 2 ^ 2) 2 br2 := by
      simpa [br1, br2, hread0, hread1] using hstep1
    _ = Huffman.decodeFuel fixedLitLenHuffman 6 (bitsTot % 2 ^ 3) 3 br3 := hstep2
    _ = Huffman.decodeFuel fixedLitLenHuffman 5 (bitsTot % 2 ^ 4) 4 br4 := hstep3
    _ = Huffman.decodeFuel fixedLitLenHuffman 4 (bitsTot % 2 ^ 5) 5 br5 := hstep4
    _ = Huffman.decodeFuel fixedLitLenHuffman 3 (bitsTot % 2 ^ 6) 6 br6 := hstep5
    _ = Huffman.decodeFuel fixedLitLenHuffman 2 (bitsTot % 2 ^ 7) 7 br7 := hstep6
    _ = Huffman.decodeFuel fixedLitLenHuffman 1 (bitsTot % 2 ^ 8) 8 br8 := hstep7
    _ = some (sym, br9) := hstep8

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Instantiates the 8-bit core decoder for low literal symbols `0..143`. -/
lemma fixedLitLenHuffman_decode_readerAt_writeBits_lo
    (bw : BitWriter) (sym restBits restLen : Nat)
    (h143 : sym ≤ 143) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let code := sym + 48
    let bits := reverseBits code 8
    let bitsTot := bits ||| (restBits <<< 8)
    let lenTot := 8 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br8 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 8) bw'.flush
      (by
        have hk : 8 ≤ lenTot := by omega
        simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 8 lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot 8 hbit)
    fixedLitLenHuffman.decode br0 = some (sym, br8) := by
  let code := sym + 48
  let bits := reverseBits code 8
  let bitsTot := bits ||| (restBits <<< 8)
  have hbits7_eq : bitsTot % 2 ^ 7 = bits % 2 ^ 7 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 7 8 (by decide))
  have hbits7_lt : bitsTot % 2 ^ 7 < fixedLitLenRow7.size := by
    have hlt : bits % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
    simpa [hbits7_eq, fixedLitLenRow7_size, Nat.shiftLeft_eq] using hlt
  have hcode8 : code < 2 ^ 8 := by
    have hlt : code < 192 := by omega
    exact lt_of_lt_of_le hlt (by decide : 192 ≤ 2 ^ 8)
  have hrev7 : reverseBits (bits % 2 ^ 7) 7 = code >>> 1 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 8) (k := 7) hcode8 (by decide))
  have h24 : 24 ≤ code >>> 1 := by
    have hdiv : 24 ≤ code / 2 := by
      have h48 : 48 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2
        (by simpa [Nat.mul_comm] using h48)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow7' : fixedLitLenRow7[bitsTot % 2 ^ 7]'hbits7_lt = none := by
    have h24' : 24 ≤ reverseBits (bitsTot % 2 ^ 7) 7 := by
      simpa [hbits7_eq, hrev7] using h24
    exact fixedLitLenRow7_get_none_of_ge (bits := bitsTot % 2 ^ 7) hbits7_lt h24'
  have hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some none := by
    simp [hbits7_lt, hrow7']
  have hbits8_eq' : bitsTot % 2 ^ 8 = bits := by
    have hlt : bits < 2 ^ 8 := by simpa [bits] using (reverseBits_lt code 8)
    have hmod' : bits % 2 ^ 8 = bits := Nat.mod_eq_of_lt hlt
    have hmod := mod_two_pow_or_shift bits restBits 8 8 (by decide)
    simpa [bitsTot, hmod'] using hmod
  have hbits8_lt : bitsTot % 2 ^ 8 < fixedLitLenRow8.size := by
    have hlt : bits < 2 ^ 8 := by simpa [bits] using (reverseBits_lt code 8)
    have hlt' : bitsTot % 2 ^ 8 < 2 ^ 8 := by
      simpa [hbits8_eq', bitsTot] using hlt
    simpa [fixedLitLenRow8_size, Nat.shiftLeft_eq] using hlt'
  have hrow8' : fixedLitLenRow8[bitsTot % 2 ^ 8]'hbits8_lt = some sym := by
    have hrow := fixedLitLenCode_row_lo (sym := sym) h143
    simpa [code, bits, hbits8_eq'] using hrow
  have hrow8 : fixedLitLenRow8[bitsTot % 2 ^ 8]? = some (some sym) := by
    simp [hbits8_lt, hrow8']
  simpa [bitsTot, code, bits] using
    (fixedLitLenHuffman_decode_readerAt_writeBits_len8_core
      (bw := bw) (sym := sym) (bitsTot := bitsTot) (restLen := restLen)
      hrow7 hrow8 hbit hcur)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Instantiates the 9-bit core decoder for middle literal symbols `144..255`. -/
lemma fixedLitLenHuffman_decode_readerAt_writeBits_mid
    (bw : BitWriter) (sym restBits restLen : Nat)
    (h144 : 144 ≤ sym) (h255 : sym ≤ 255) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let code := sym - 144 + 400
    let bits := reverseBits code 9
    let bitsTot := bits ||| (restBits <<< 9)
    let lenTot := 9 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br9 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 9) bw'.flush
      (by
        have hk : 9 ≤ lenTot := by omega
        simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 9 lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot 9 hbit)
    fixedLitLenHuffman.decode br0 = some (sym, br9) := by
  let code := sym - 144 + 400
  let bits := reverseBits code 9
  let bitsTot := bits ||| (restBits <<< 9)
  have hbits7_eq : bitsTot % 2 ^ 7 = bits % 2 ^ 7 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 7 9 (by decide))
  have hbits7_lt : bitsTot % 2 ^ 7 < fixedLitLenRow7.size := by
    have hlt : bits % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
    simpa [hbits7_eq, fixedLitLenRow7_size, Nat.shiftLeft_eq] using hlt
  have hcode9 : code < 2 ^ 9 := by
    have hlt : code < 512 := by omega
    exact lt_of_lt_of_le hlt (by decide : 512 ≤ 2 ^ 9)
  have hrev7 : reverseBits (bits % 2 ^ 7) 7 = code >>> 2 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 9) (k := 7) hcode9 (by decide))
  have h24 : 24 ≤ code >>> 2 := by
    have hdiv : 24 ≤ code / 4 := by
      have h96 : 96 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (4 : Nat))).2
        (by simpa [Nat.mul_comm] using h96)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow7' : fixedLitLenRow7[bitsTot % 2 ^ 7]'hbits7_lt = none := by
    have h24' : 24 ≤ reverseBits (bitsTot % 2 ^ 7) 7 := by
      simpa [hbits7_eq, hrev7] using h24
    exact fixedLitLenRow7_get_none_of_ge (bits := bitsTot % 2 ^ 7) hbits7_lt h24'
  have hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some none := by
    simp [hbits7_lt, hrow7']
  have hbits8_eq : bitsTot % 2 ^ 8 = bits % 2 ^ 8 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 8 9 (by decide))
  have hbits8_lt : bitsTot % 2 ^ 8 < fixedLitLenRow8.size := by
    have hlt : bits % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
    simpa [hbits8_eq, fixedLitLenRow8_size, Nat.shiftLeft_eq] using hlt
  have hrev8 : reverseBits (bits % 2 ^ 8) 8 = code >>> 1 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 9) (k := 8) hcode9 (by decide))
  have h200 : 200 ≤ code >>> 1 := by
    have hdiv : 200 ≤ code / 2 := by
      have h400 : 400 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2
        (by simpa [Nat.mul_comm] using h400)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow8' : fixedLitLenRow8[bitsTot % 2 ^ 8]'hbits8_lt = none := by
    have h200' : 200 ≤ reverseBits (bitsTot % 2 ^ 8) 8 := by
      simpa [hbits8_eq, hrev8] using h200
    exact fixedLitLenHuffman_row8_get_none_of_ge (bits := bitsTot % 2 ^ 8) hbits8_lt h200'
  have hrow8 : fixedLitLenRow8[bitsTot % 2 ^ 8]? = some none := by
    simp [hbits8_lt, hrow8']
  have hbits9_eq : bitsTot % 2 ^ 9 = bits := by
    have hlt : bits < 2 ^ 9 := by simpa [bits] using (reverseBits_lt code 9)
    have hmod' : bits % 2 ^ 9 = bits := Nat.mod_eq_of_lt hlt
    have hmod := mod_two_pow_or_shift bits restBits 9 9 (by decide)
    simpa [bitsTot, hmod'] using hmod
  have hbits9_lt : bitsTot % 2 ^ 9 < fixedLitLenRow9.size := by
    have hlt : bits < 2 ^ 9 := by simpa [bits] using (reverseBits_lt code 9)
    simpa [hbits9_eq, fixedLitLenRow9_size, Nat.shiftLeft_eq] using hlt
  have hrow9' : fixedLitLenRow9[bitsTot % 2 ^ 9]'hbits9_lt = some sym := by
    have hrow := fixedLitLenHuffman_row9_get_mid (sym := sym) h144 h255
    simpa [code, bits, hbits9_eq] using hrow
  have hrow9 : fixedLitLenRow9[bitsTot % 2 ^ 9]? = some (some sym) := by
    simp [hbits9_lt, hrow9']
  simpa [bitsTot, code, bits] using
    (fixedLitLenHuffman_decode_readerAt_writeBits_len9_core
      (bw := bw) (sym := sym) (bitsTot := bitsTot) (restLen := restLen)
      hrow7 hrow8 hrow9 hbit hcur)

/-- Covers every literal byte emitted by the dynamic encoder using the fixed literal table. -/
lemma fixedLitLenHuffman_decode_readerAt_writeBits
    (bw : BitWriter) (sym restBits restLen : Nat)
    (hsym : sym < 256) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codeLen := fixedLitLenCode sym
    let code := codeLen.1
    let len := codeLen.2
    let bits := reverseBits code len
    let bitsTot := bits ||| (restBits <<< len)
    let lenTot := len + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br1 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
      (by
        have hk : len ≤ lenTot := by omega
        simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot len hbit)
    fixedLitLenHuffman.decode br0 = some (sym, br1) := by
  classical
  by_cases h143 : sym ≤ 143
  · have hcode : fixedLitLenCode sym = (sym + 48, 8) := fixedLitLenCode_lo sym h143
    simpa [hcode] using
      (fixedLitLenHuffman_decode_readerAt_writeBits_lo
        (bw := bw) (sym := sym) (restBits := restBits) (restLen := restLen) h143 hbit hcur)
  · have h144 : 144 ≤ sym := by omega
    have h255 : sym ≤ 255 := by omega
    have hcode : fixedLitLenCode sym = (sym - 144 + 400, 9) := fixedLitLenCode_mid sym h144 h255
    simpa [hcode] using
      (fixedLitLenHuffman_decode_readerAt_writeBits_mid
        (bw := bw) (sym := sym) (restBits := restBits) (restLen := restLen) h144 h255 hbit hcur)

/-- Converts a known literal decode into one step of `decodeCompressedBlockFuel`. -/
lemma decodeCompressedBlockFuel_step_literal_of_decodes_aux
    (fuel : Nat) (litLen dist : Huffman) (br br' : BitReader)
    (out : ByteArray) (sym : Nat)
    (hdecodeSym : litLen.decode br = some (sym, br'))
    (hlit : sym < 256) :
    decodeCompressedBlockFuel (fuel + 1) litLen dist br out =
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym)) := by
  rw [decodeCompressedBlockFuel.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  let k : Nat → BitReader → Option (BitReader × ByteArray) := fun sym br' =>
    if sym < 256 then
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
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
          let (distSym, br''') ← dist.decode br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeCompressedBlockFuel fuel litLen dist br'''' out'
            else
              none
          else
            none
      else
        none
    else
      none
  change (match (sym, br') with | (s, r) => k s r) =
    decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
  have hpair : (match (sym, br') with | (s, r) => k s r) = k sym br' := by
    simpa using (match_pair_eta (a := sym) (b := br') (k := k))
  rw [hpair]
  dsimp [k]
  rw [if_pos hlit]

set_option maxRecDepth 200000 in
/-- Replays one low-literal step on the exact reader produced by `writeBits`. -/
lemma decodeCompressedBlockFuel_step_literal_readerAt_writeBits_lo
    (fuel : Nat) (bw : BitWriter) (sym restBits restLen : Nat) (dist : Huffman) (out : ByteArray)
    (h143 : sym ≤ 143) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let code := sym + 48
    let bits := reverseBits code 8
    let bitsTot := bits ||| (restBits <<< 8)
    let lenTot := 8 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br8 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 8) bw'.flush
      (by
        have hk : 8 ≤ lenTot := by omega
        simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 8 lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot 8 hbit)
    decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist br0 out =
      decodeCompressedBlockFuel fuel fixedLitLenHuffman dist br8 (out.push (u8 sym)) := by
  have hdecodeSym :=
    fixedLitLenHuffman_decode_readerAt_writeBits_lo
      (bw := bw) (sym := sym) (restBits := restBits) (restLen := restLen)
      h143 hbit hcur
  have hlit : sym < 256 := by omega
  simpa using
    (decodeCompressedBlockFuel_step_literal_of_decodes_aux
      (fuel := fuel) (litLen := fixedLitLenHuffman) (dist := dist)
      (br := BitWriter.readerAt bw
        (BitWriter.writeBits bw
          ((reverseBits (sym + 48) 8) ||| (restBits <<< 8))
          (8 + restLen)).flush
        (flush_size_writeBits_le bw
          ((reverseBits (sym + 48) 8) ||| (restBits <<< 8))
          (8 + restLen)) hbit)
      (br' := BitWriter.readerAt
        (BitWriter.writeBits bw
          ((reverseBits (sym + 48) 8) ||| (restBits <<< 8)) 8)
        (BitWriter.writeBits bw
          ((reverseBits (sym + 48) 8) ||| (restBits <<< 8))
          (8 + restLen)).flush
        (by
          have hk : 8 ≤ 8 + restLen := by omega
          simpa using
            (flush_size_writeBits_prefix bw
              ((reverseBits (sym + 48) 8) ||| (restBits <<< 8)) 8 (8 + restLen) hk))
        (bitPos_lt_8_writeBits bw
          ((reverseBits (sym + 48) 8) ||| (restBits <<< 8)) 8 hbit))
      (out := out) (sym := sym) (hdecodeSym := by simpa using hdecodeSym) (hlit := hlit))

/-- Replays one literal step for any byte emitted with the fixed literal table. -/
lemma decodeCompressedBlockFuel_step_literal_readerAt_writeBits
    (fuel : Nat) (bw : BitWriter) (sym restBits restLen : Nat) (dist : Huffman) (out : ByteArray)
    (hsym : sym < 256) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codeLen := fixedLitLenCode sym
    let code := codeLen.1
    let len := codeLen.2
    let bits := reverseBits code len
    let bitsTot := bits ||| (restBits <<< len)
    let lenTot := len + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br1 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
      (by
        have hk : len ≤ lenTot := by omega
        simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot len hbit)
    decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist br0 out =
      decodeCompressedBlockFuel fuel fixedLitLenHuffman dist br1 (out.push (u8 sym)) := by
  have hdecodeSym :=
    fixedLitLenHuffman_decode_readerAt_writeBits
      (bw := bw) (sym := sym) (restBits := restBits) (restLen := restLen)
      hsym hbit hcur
  simpa using
    (decodeCompressedBlockFuel_step_literal_of_decodes_aux
      (fuel := fuel) (litLen := fixedLitLenHuffman) (dist := dist)
      (br := BitWriter.readerAt bw
        (BitWriter.writeBits bw
          ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
            (restBits <<< (fixedLitLenCode sym).2))
          ((fixedLitLenCode sym).2 + restLen)).flush
        (flush_size_writeBits_le bw
          ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
            (restBits <<< (fixedLitLenCode sym).2))
          ((fixedLitLenCode sym).2 + restLen)) hbit)
      (br' := BitWriter.readerAt
        (BitWriter.writeBits bw
          ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
            (restBits <<< (fixedLitLenCode sym).2))
          (fixedLitLenCode sym).2)
        (BitWriter.writeBits bw
          ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
            (restBits <<< (fixedLitLenCode sym).2))
          ((fixedLitLenCode sym).2 + restLen)).flush
        (by
          have hk : (fixedLitLenCode sym).2 ≤ (fixedLitLenCode sym).2 + restLen := by omega
          simpa using
            (flush_size_writeBits_prefix bw
              ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
                (restBits <<< (fixedLitLenCode sym).2))
              (fixedLitLenCode sym).2 ((fixedLitLenCode sym).2 + restLen) hk))
        (bitPos_lt_8_writeBits bw
          ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
            (restBits <<< (fixedLitLenCode sym).2))
          (fixedLitLenCode sym).2 hbit))
      (out := out) (sym := sym) (hdecodeSym := by simpa using hdecodeSym) (hlit := hsym))

/-- General literal-step lemma used after the payload decoder has already identified a byte symbol. -/
lemma decodeCompressedBlockFuel_step_literal_of_decodes
    (fuel : Nat) (litLen dist : Huffman) (br br' : BitReader)
    (out : ByteArray) (sym : Nat)
    (hdecodeSym : litLen.decode br = some (sym, br'))
    (hlit : sym < 256) :
    decodeCompressedBlockFuel (fuel + 1) litLen dist br out =
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym)) := by
  rw [decodeCompressedBlockFuel.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  let k : Nat → BitReader → Option (BitReader × ByteArray) := fun sym br' =>
    if sym < 256 then
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
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
          let (distSym, br''') ← dist.decode br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeCompressedBlockFuel fuel litLen dist br'''' out'
            else
              none
          else
            none
      else
        none
    else
      none
  change (match (sym, br') with | (s, r) => k s r) =
    decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
  have hpair : (match (sym, br') with | (s, r) => k s r) = k sym br' := by
    simpa using (match_pair_eta (a := sym) (b := br') (k := k))
  rw [hpair]
  dsimp [k]
  rw [if_pos hlit]

set_option maxRecDepth 200000 in
/-- Converts a known EOB decode into the terminating branch of `decodeCompressedBlockFuel`. -/
lemma decodeCompressedBlockFuel_step_eob_of_decodes
    (fuel : Nat) (litLen dist : Huffman) (br br' : BitReader)
    (out : ByteArray) (sym : Nat)
    (hdecodeSym : litLen.decode br = some (sym, br'))
    (hnotLit : ¬ sym < 256) (heob : (sym == 256) = true) :
    decodeCompressedBlockFuel (fuel + 1) litLen dist br out = some (br', out) := by
  rw [decodeCompressedBlockFuel.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  let k : Nat → BitReader → Option (BitReader × ByteArray) := fun sym br' =>
    if sym < 256 then
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
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
          let (distSym, br''') ← dist.decode br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeCompressedBlockFuel fuel litLen dist br'''' out'
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
  rw [if_neg hnotLit, if_pos heob]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Decodes the fixed-table end-of-block marker when it is written with no trailing payload bits. -/
lemma fixedLitLenHuffman_decode_eobNoTail
    (bw : BitWriter) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    fixedLitLenHuffman.decode (eobNoTailStartReader bw hbit) =
      some (256, eobNoTailAfterReader bw hbit) := by
  let bwAll := BitWriter.writeBits bw 0 7
  let bw1 := BitWriter.writeBits bw 0 1
  let bw2 := BitWriter.writeBits bw 0 2
  let bw3 := BitWriter.writeBits bw 0 3
  let bw4 := BitWriter.writeBits bw 0 4
  let bw5 := BitWriter.writeBits bw 0 5
  let bw6 := BitWriter.writeBits bw 0 6
  let br0 := eobNoTailStartReader bw hbit
  have hsplit1 : bwAll = BitWriter.writeBits bw1 0 6 := by
    simpa [bwAll, bw1] using (writeBits_split bw 0 1 6)
  have hsplit2 : bwAll = BitWriter.writeBits bw2 0 5 := by
    simpa [bwAll, bw2] using (writeBits_split bw 0 2 5)
  have hsplit3 : bwAll = BitWriter.writeBits bw3 0 4 := by
    simpa [bwAll, bw3] using (writeBits_split bw 0 3 4)
  have hsplit4 : bwAll = BitWriter.writeBits bw4 0 3 := by
    simpa [bwAll, bw4] using (writeBits_split bw 0 4 3)
  have hsplit5 : bwAll = BitWriter.writeBits bw5 0 2 := by
    simpa [bwAll, bw5] using (writeBits_split bw 0 5 2)
  have hsplit6 : bwAll = BitWriter.writeBits bw6 0 1 := by
    simpa [bwAll, bw6] using (writeBits_split bw 0 6 1)
  let br1 := BitWriter.readerAt bw1 bwAll.flush
    (by
      simpa [hsplit1] using (flush_size_writeBits_le (bw := bw1) (bits := 0) (len := 6)))
    (by
      simpa [bw1] using bitPos_lt_8_writeBits bw 0 1 hbit)
  let br2 := BitWriter.readerAt bw2 bwAll.flush
    (by
      simpa [hsplit2] using (flush_size_writeBits_le (bw := bw2) (bits := 0) (len := 5)))
    (by
      simpa [bw2] using bitPos_lt_8_writeBits bw 0 2 hbit)
  let br3 := BitWriter.readerAt bw3 bwAll.flush
    (by
      simpa [hsplit3] using (flush_size_writeBits_le (bw := bw3) (bits := 0) (len := 4)))
    (by
      simpa [bw3] using bitPos_lt_8_writeBits bw 0 3 hbit)
  let br4 := BitWriter.readerAt bw4 bwAll.flush
    (by
      simpa [hsplit4] using (flush_size_writeBits_le (bw := bw4) (bits := 0) (len := 3)))
    (by
      simpa [bw4] using bitPos_lt_8_writeBits bw 0 4 hbit)
  let br5 := BitWriter.readerAt bw5 bwAll.flush
    (by
      simpa [hsplit5] using (flush_size_writeBits_le (bw := bw5) (bits := 0) (len := 2)))
    (by
      simpa [bw5] using bitPos_lt_8_writeBits bw 0 5 hbit)
  let br6 := BitWriter.readerAt bw6 bwAll.flush
    (by
      simpa [hsplit6] using (flush_size_writeBits_le (bw := bw6) (bits := 0) (len := 1)))
    (by
      simpa [bw6] using bitPos_lt_8_writeBits bw 0 6 hbit)
  let br7 := eobNoTailAfterReader bw hbit
  have hcur1 : bw1.curClearAbove := by
    simpa [bw1] using curClearAbove_writeBits bw 0 1 hbit hcur
  have hcur2 : bw2.curClearAbove := by
    simpa [bw2] using curClearAbove_writeBits bw 0 2 hbit hcur
  have hcur3 : bw3.curClearAbove := by
    simpa [bw3] using curClearAbove_writeBits bw 0 3 hbit hcur
  have hcur4 : bw4.curClearAbove := by
    simpa [bw4] using curClearAbove_writeBits bw 0 4 hbit hcur
  have hcur5 : bw5.curClearAbove := by
    simpa [bw5] using curClearAbove_writeBits bw 0 5 hbit hcur
  have hcur6 : bw6.curClearAbove := by
    simpa [bw6] using curClearAbove_writeBits bw 0 6 hbit hcur
  have hbound0 : br0.bitIndex + 1 ≤ br0.data.size * 8 := by
    simpa [br0, eobNoTailStartReader, eobNoTailWriter, bwAll, BitWriter.writeBits] using
      (readerAt_writeBits_bound (bw := bw) (bits := 0) (len := 7) (k := 1) (by decide) hbit)
  have hbound1 : br1.bitIndex + 1 ≤ br1.data.size * 8 := by
    simpa [br1, hsplit1] using
      (readerAt_writeBits_bound (bw := bw1) (bits := 0) (len := 6) (k := 1) (by decide)
        (by simpa [bw1] using bitPos_lt_8_writeBits bw 0 1 hbit))
  have hbound2 : br2.bitIndex + 1 ≤ br2.data.size * 8 := by
    simpa [br2, hsplit2] using
      (readerAt_writeBits_bound (bw := bw2) (bits := 0) (len := 5) (k := 1) (by decide)
        (by simpa [bw2] using bitPos_lt_8_writeBits bw 0 2 hbit))
  have hbound3 : br3.bitIndex + 1 ≤ br3.data.size * 8 := by
    simpa [br3, hsplit3] using
      (readerAt_writeBits_bound (bw := bw3) (bits := 0) (len := 4) (k := 1) (by decide)
        (by simpa [bw3] using bitPos_lt_8_writeBits bw 0 3 hbit))
  have hbound4 : br4.bitIndex + 1 ≤ br4.data.size * 8 := by
    simpa [br4, hsplit4] using
      (readerAt_writeBits_bound (bw := bw4) (bits := 0) (len := 3) (k := 1) (by decide)
        (by simpa [bw4] using bitPos_lt_8_writeBits bw 0 4 hbit))
  have hbound5 : br5.bitIndex + 1 ≤ br5.data.size * 8 := by
    simpa [br5, hsplit5] using
      (readerAt_writeBits_bound (bw := bw5) (bits := 0) (len := 2) (k := 1) (by decide)
        (by simpa [bw5] using bitPos_lt_8_writeBits bw 0 5 hbit))
  have hbound6 : br6.bitIndex + 1 ≤ br6.data.size * 8 := by
    simpa [br6, hsplit6] using
      (readerAt_writeBits_bound (bw := bw6) (bits := 0) (len := 1) (k := 1) (by decide)
        (by simpa [bw6] using bitPos_lt_8_writeBits bw 0 6 hbit))
  have hbr0 : br0.bytePos < br0.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br0 (by omega)
  have hbr1 : br1.bytePos < br1.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br1 (by omega)
  have hbr2 : br2.bytePos < br2.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br2 (by omega)
  have hbr3 : br3.bytePos < br3.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br3 (by omega)
  have hbr4 : br4.bytePos < br4.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br4 (by omega)
  have hbr5 : br5.bytePos < br5.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br5 (by omega)
  have hbr6 : br6.bytePos < br6.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br6 (by omega)
  have hread0 :
      br0.readBit = (0, br1) := by
    simpa [br0, br1, eobNoTailStartReader, eobNoTailWriter, bwAll, bw1, BitWriter.writeBits, hsplit1] using
      (readBit_readerAt_writeBits (bw := bw) (bits := 0) (len := 7) hbit hcur (by decide))
  have hread1 :
      br1.readBit = (0, br2) := by
    simpa [br1, br2, bw1, bw2, BitWriter.writeBits, hsplit1, hsplit2] using
      (readBit_readerAt_writeBits (bw := bw1) (bits := 0) (len := 6)
        (by simpa [bw1] using bitPos_lt_8_writeBits bw 0 1 hbit) hcur1 (by decide))
  have hread2 :
      br2.readBit = (0, br3) := by
    simpa [br2, br3, bw2, bw3, BitWriter.writeBits, hsplit2, hsplit3] using
      (readBit_readerAt_writeBits (bw := bw2) (bits := 0) (len := 5)
        (by simpa [bw2] using bitPos_lt_8_writeBits bw 0 2 hbit) hcur2 (by decide))
  have hread3 :
      br3.readBit = (0, br4) := by
    simpa [br3, br4, bw3, bw4, BitWriter.writeBits, hsplit3, hsplit4] using
      (readBit_readerAt_writeBits (bw := bw3) (bits := 0) (len := 4)
        (by simpa [bw3] using bitPos_lt_8_writeBits bw 0 3 hbit) hcur3 (by decide))
  have hread4 :
      br4.readBit = (0, br5) := by
    simpa [br4, br5, bw4, bw5, BitWriter.writeBits, hsplit4, hsplit5] using
      (readBit_readerAt_writeBits (bw := bw4) (bits := 0) (len := 3)
        (by simpa [bw4] using bitPos_lt_8_writeBits bw 0 4 hbit) hcur4 (by decide))
  have hread5 :
      br5.readBit = (0, br6) := by
    simpa [br5, br6, bw5, bw6, BitWriter.writeBits, hsplit5, hsplit6] using
      (readBit_readerAt_writeBits (bw := bw5) (bits := 0) (len := 2)
        (by simpa [bw5] using bitPos_lt_8_writeBits bw 0 5 hbit) hcur5 (by decide))
  have hread6 :
      br6.readBit = (0, br7) := by
    simpa [br6, br7, eobNoTailAfterReader, eobNoTailWriter, bwAll, bw6, BitWriter.writeBits, hsplit6] using
      (readBit_readerAt_writeBits (bw := bw6) (bits := 0) (len := 1)
        (by simpa [bw6] using bitPos_lt_8_writeBits bw 0 6 hbit) hcur6 (by decide))
  have htable1 : 1 < fixedLitLenHuffman.table.size := by native_decide
  have htable2 : 2 < fixedLitLenHuffman.table.size := by native_decide
  have htable3 : 3 < fixedLitLenHuffman.table.size := by native_decide
  have htable4 : 4 < fixedLitLenHuffman.table.size := by native_decide
  have htable5 : 5 < fixedLitLenHuffman.table.size := by native_decide
  have htable6 : 6 < fixedLitLenHuffman.table.size := by native_decide
  have htable7 : 7 < fixedLitLenHuffman.table.size := by native_decide
  have hcode1 : 0 < (Array.getInternal fixedLitLenHuffman.table 1 htable1).size := by
    have hcode1' :
        0 < (Array.getInternal fixedLitLenHuffman.table 1
          (by native_decide : 1 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode1'
  have hcode2 : 0 < (Array.getInternal fixedLitLenHuffman.table 2 htable2).size := by
    have hcode2' :
        0 < (Array.getInternal fixedLitLenHuffman.table 2
          (by native_decide : 2 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode2'
  have hcode3 : 0 < (Array.getInternal fixedLitLenHuffman.table 3 htable3).size := by
    have hcode3' :
        0 < (Array.getInternal fixedLitLenHuffman.table 3
          (by native_decide : 3 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode3'
  have hcode4 : 0 < (Array.getInternal fixedLitLenHuffman.table 4 htable4).size := by
    have hcode4' :
        0 < (Array.getInternal fixedLitLenHuffman.table 4
          (by native_decide : 4 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode4'
  have hcode5 : 0 < (Array.getInternal fixedLitLenHuffman.table 5 htable5).size := by
    have hcode5' :
        0 < (Array.getInternal fixedLitLenHuffman.table 5
          (by native_decide : 5 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode5'
  have hcode6 : 0 < (Array.getInternal fixedLitLenHuffman.table 6 htable6).size := by
    have hcode6' :
        0 < (Array.getInternal fixedLitLenHuffman.table 6
          (by native_decide : 6 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode6'
  have hcode7 : 0 < (Array.getInternal fixedLitLenHuffman.table 7 htable7).size := by
    have hcode7' :
        0 < (Array.getInternal fixedLitLenHuffman.table 7
          (by native_decide : 7 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode7'
  have hrow1 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 1 htable1) 0 hcode1 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 1) (code := 0) (by decide) (by decide) hcode1
  have hrow2 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 2 htable2) 0 hcode2 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 2) (code := 0) (by decide) (by decide) hcode2
  have hrow3 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 3 htable3) 0 hcode3 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 3) (code := 0) (by decide) (by decide) hcode3
  have hrow4 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 4 htable4) 0 hcode4 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 4) (code := 0) (by decide) (by decide) hcode4
  have hrow5 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 5 htable5) 0 hcode5 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 5) (code := 0) (by decide) (by decide) hcode5
  have hrow6 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 6 htable6) 0 hcode6 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 6) (code := 0) (by decide) (by decide) hcode6
  have hrow7 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 7 htable7) 0 hcode7 = some 256 := by
    simpa using fixedLitLenHuffman_row7_get_eob
  have hstep0 :
      fixedLitLenHuffman.decode br0 =
        Huffman.decodeFuel fixedLitLenHuffman 8 0 1 br1 := by
    unfold Huffman.decode
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 8) (code := 0) (len := 0)
        (br := br0) (br' := br1) (bit := 0)
        (hbyte := hbr0) (hread := hread0) (htable := htable1) (hcode := hcode1) (hrow := hrow1))
  have hstep1 :
      Huffman.decodeFuel fixedLitLenHuffman 8 0 1 br1 =
        Huffman.decodeFuel fixedLitLenHuffman 7 0 2 br2 := by
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 7) (code := 0) (len := 1)
        (br := br1) (br' := br2) (bit := 0)
        (hbyte := hbr1) (hread := hread1) (htable := htable2) (hcode := hcode2) (hrow := hrow2))
  have hstep2 :
      Huffman.decodeFuel fixedLitLenHuffman 7 0 2 br2 =
        Huffman.decodeFuel fixedLitLenHuffman 6 0 3 br3 := by
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 6) (code := 0) (len := 2)
        (br := br2) (br' := br3) (bit := 0)
        (hbyte := hbr2) (hread := hread2) (htable := htable3) (hcode := hcode3) (hrow := hrow3))
  have hstep3 :
      Huffman.decodeFuel fixedLitLenHuffman 6 0 3 br3 =
        Huffman.decodeFuel fixedLitLenHuffman 5 0 4 br4 := by
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 5) (code := 0) (len := 3)
        (br := br3) (br' := br4) (bit := 0)
        (hbyte := hbr3) (hread := hread3) (htable := htable4) (hcode := hcode4) (hrow := hrow4))
  have hstep4 :
      Huffman.decodeFuel fixedLitLenHuffman 5 0 4 br4 =
        Huffman.decodeFuel fixedLitLenHuffman 4 0 5 br5 := by
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 4) (code := 0) (len := 4)
        (br := br4) (br' := br5) (bit := 0)
        (hbyte := hbr4) (hread := hread4) (htable := htable5) (hcode := hcode5) (hrow := hrow5))
  have hstep5 :
      Huffman.decodeFuel fixedLitLenHuffman 4 0 5 br5 =
        Huffman.decodeFuel fixedLitLenHuffman 3 0 6 br6 := by
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 3) (code := 0) (len := 5)
        (br := br5) (br' := br6) (bit := 0)
        (hbyte := hbr5) (hread := hread5) (htable := htable6) (hcode := hcode6) (hrow := hrow6))
  have hstep6 :
      Huffman.decodeFuel fixedLitLenHuffman 3 0 6 br6 = some (256, br7) := by
    simpa using
      (Huffman.decodeFuel_step_some (h := fixedLitLenHuffman) (fuel := 2) (code := 0) (len := 6)
        (br := br6) (br' := br7) (bit := 0) (sym := 256)
        (hbyte := hbr6) (hread := hread6) (htable := htable7) (hcode := hcode7) (hrow := hrow7))
  calc
    fixedLitLenHuffman.decode br0 = Huffman.decodeFuel fixedLitLenHuffman 8 0 1 br1 := hstep0
    _ = Huffman.decodeFuel fixedLitLenHuffman 7 0 2 br2 := hstep1
    _ = Huffman.decodeFuel fixedLitLenHuffman 6 0 3 br3 := hstep2
    _ = Huffman.decodeFuel fixedLitLenHuffman 5 0 4 br4 := hstep3
    _ = Huffman.decodeFuel fixedLitLenHuffman 4 0 5 br5 := hstep4
    _ = Huffman.decodeFuel fixedLitLenHuffman 3 0 6 br6 := hstep5
    _ = some (256, br7) := hstep6

set_option maxRecDepth 200000 in
/-- Replays the terminating EOB step of `decodeCompressedBlockFuel` on the no-tail reader. -/
lemma decodeCompressedBlockFuel_step_eob_eobNoTail
    (fuel : Nat) (bw : BitWriter) (dist : Huffman) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist (eobNoTailStartReader bw hbit) out =
      some (eobNoTailAfterReader bw hbit, out) := by
  have hdecodeSym : fixedLitLenHuffman.decode (eobNoTailStartReader bw hbit) =
      some (256, eobNoTailAfterReader bw hbit) := by
    exact fixedLitLenHuffman_decode_eobNoTail (bw := bw) (hbit := hbit) (hcur := hcur)
  have hnotLit : ¬ (256 : Nat) < 256 := by decide
  have heob : ((256 : Nat) == 256) = true := by decide
  simpa using
    (decodeCompressedBlockFuel_step_eob_of_decodes
      (fuel := fuel) (litLen := fixedLitLenHuffman) (dist := dist)
      (br := eobNoTailStartReader bw hbit) (br' := eobNoTailAfterReader bw hbit)
      (out := out) (sym := 256) (hdecodeSym := hdecodeSym) (hnotLit := hnotLit) (heob := heob))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Proves that decoding the fixed literal payload followed by EOB reconstructs the original bytes. -/
lemma decodeCompressedBlock_fixedLitBitsEob
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (dist : Huffman)
    (out : ByteArray) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsLen := fixedLitBitsEob data i
    let bits := bitsLen.1
    let len := bitsLen.2
    let bw' := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
    decodeCompressedBlock fixedLitLenHuffman dist br out =
      some
        (BitWriter.readerAt (BitWriter.writeBits bw bits len) bw'.flush
          (by
            simpa [bw'] using
              (le_rfl : (BitWriter.writeBits bw bits len).flush.size ≤
                (BitWriter.writeBits bw bits len).flush.size))
          (bitPos_lt_8_writeBits bw bits len hbit),
        byteArrayFromArray data i out) := by
  classical
  have hk :
      ∀ k, ∀ i bw out (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove), data.size - i = k →
        ∀ fuel, k + 1 ≤ fuel →
          let bitsLen := fixedLitBitsEob data i
          let bits := bitsLen.1
          let len := bitsLen.2
          let bw' := BitWriter.writeBits bw bits len
          let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
          decodeCompressedBlockFuel fuel fixedLitLenHuffman dist br out =
            some
              (BitWriter.readerAt (BitWriter.writeBits bw bits len) bw'.flush
                (by
                  simpa [bw'] using
                    (le_rfl : (BitWriter.writeBits bw bits len).flush.size ≤
                      (BitWriter.writeBits bw bits len).flush.size))
                (bitPos_lt_8_writeBits bw bits len hbit),
              byteArrayFromArray data i out) := by
    intro k
    induction k with
    | zero =>
        intro i bw out hbit hcur hk fuel hfuel
        cases fuel with
        | zero =>
            have : (1 : Nat) ≤ 0 := by simpa using hfuel
            exact (False.elim (Nat.not_succ_le_zero 0 this))
        | succ fuel =>
            have hle : data.size ≤ i := Nat.le_of_sub_eq_zero hk
            have hlt : ¬ i < data.size := not_lt_of_ge hle
            simpa [fixedLitBitsEob, hlt, byteArrayFromArray, eobNoTailWriter,
                eobNoTailStartReader, eobNoTailAfterReader] using
              (decodeCompressedBlockFuel_step_eob_eobNoTail
                (fuel := fuel) (bw := bw) (dist := dist) (out := out) hbit hcur)
    | succ k ih =>
        intro i bw out hbit hcur hk fuel hfuel
        cases fuel with
        | zero =>
            have : (k + 2) ≤ 0 := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfuel
            exact (False.elim (Nat.not_succ_le_zero _ this))
        | succ fuel =>
            have hlt : i < data.size := by
              have hpos : 0 < data.size - i := by omega
              exact (Nat.sub_pos_iff_lt).1 hpos
            have hk' : data.size - (i + 1) = k := by omega
            let b := data[i]
            let codeLen := fixedLitLenCode b.toNat
            let code := codeLen.1
            let len := codeLen.2
            let bits := reverseBits code len
            let rest := fixedLitBitsEob data (i + 1)
            let restBits := rest.1
            let restLen := rest.2
            let bitsTot := bits ||| (restBits <<< len)
            let lenTot := len + restLen
            let bw' := BitWriter.writeBits bw bitsTot lenTot
            let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
            have hbitsLen : fixedLitBitsEob data i = (bitsTot, lenTot) := by
              rw [fixedLitBitsEob]
              simp [hlt, bitsTot, lenTot, b, codeLen, code, len, bits, rest, restBits, restLen]
            have hsym : b.toNat < 256 := by
              simpa using (UInt8.toNat_lt b)
            have hdecode :=
              decodeCompressedBlockFuel_step_literal_readerAt_writeBits
                (fuel := fuel) (bw := bw) (sym := b.toNat)
                (restBits := restBits) (restLen := restLen)
                (dist := dist) (out := out) hsym hbit hcur
            have hbits : bits < 2 ^ len := by
              simpa [bits] using (reverseBits_lt code len)
            have hconcat :
                BitWriter.writeBits bw bitsTot lenTot =
                  BitWriter.writeBits (BitWriter.writeBits bw bits len) restBits restLen := by
              simpa [bitsTot, lenTot] using (writeBits_concat bw bits restBits len restLen hbits)
            have hmod : bitsTot % 2 ^ len = bits := by
              have hmod' : bitsTot % 2 ^ len = bits % 2 ^ len := by
                simpa [bitsTot] using
                  (mod_two_pow_or_shift (a := bits) (b := restBits) (k := len) (len := len) (hk := le_rfl))
              have hbitsmod : bits % 2 ^ len = bits := Nat.mod_eq_of_lt hbits
              simpa [hbitsmod] using hmod'
            have hwriteBits : BitWriter.writeBits bw bitsTot len = BitWriter.writeBits bw bits len := by
              calc
                BitWriter.writeBits bw bitsTot len
                    = BitWriter.writeBits bw (bitsTot % 2 ^ len) len := by
                        simpa using (writeBits_mod bw bitsTot len)
                _ = BitWriter.writeBits bw bits len := by
                        simp [hmod]
            have hih :=
              ih (i := i + 1) (bw := BitWriter.writeBits bw bits len)
                (out := out.push (u8 b.toNat))
                (hbit := bitPos_lt_8_writeBits bw bits len hbit)
                (hcur := curClearAbove_writeBits bw bits len hbit hcur) hk' fuel (by
                  have : k + 2 ≤ Nat.succ fuel := by
                    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfuel
                  exact Nat.succ_le_succ_iff.mp this)
            have hih' :
                decodeCompressedBlockFuel fuel fixedLitLenHuffman dist
                    (BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
                      (by
                        have hk : len ≤ lenTot := by omega
                        simpa [bw', lenTot] using
                          (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
                      (bitPos_lt_8_writeBits bw bitsTot len hbit))
                    (out.push (u8 b.toNat)) =
                  some
                    (BitWriter.readerAt (BitWriter.writeBits bw bitsTot lenTot) bw'.flush
                      (by
                        simpa [bw'] using
                          (le_rfl : (BitWriter.writeBits bw bitsTot lenTot).flush.size ≤
                            (BitWriter.writeBits bw bitsTot lenTot).flush.size))
                      (bitPos_lt_8_writeBits bw bitsTot lenTot hbit),
                    byteArrayFromArray data (i + 1) (out.push (u8 b.toNat))) := by
              simpa [bitsTot, lenTot, bw', hconcat, hwriteBits] using hih
            have hdecode' :
                decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist br out =
                  decodeCompressedBlockFuel fuel fixedLitLenHuffman dist
                    (BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
                      (by
                        have hk : len ≤ lenTot := by omega
                        simpa [bw', lenTot] using
                          (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
                      (bitPos_lt_8_writeBits bw bitsTot len hbit))
                    (out.push (u8 b.toNat)) := by
              simpa [bitsTot, lenTot, bw', br, codeLen, code, len, bits, rest, restBits, restLen] using hdecode
            have hstep :
                byteArrayFromArray data i out =
                  byteArrayFromArray data (i + 1) (out.push (u8 b.toNat)) := by
              rw [byteArrayFromArray_unfold]
              simp [hlt, b, u8]
            have hcalc :
                decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist br out =
                  some
                    (BitWriter.readerAt (BitWriter.writeBits bw bitsTot lenTot) bw'.flush
                      (by
                        simpa [bw'] using
                          (le_rfl : (BitWriter.writeBits bw bitsTot lenTot).flush.size ≤
                            (BitWriter.writeBits bw bitsTot lenTot).flush.size))
                      (bitPos_lt_8_writeBits bw bitsTot lenTot hbit),
                    byteArrayFromArray data i out) := by
              calc
                decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist br out
                    = decodeCompressedBlockFuel fuel fixedLitLenHuffman dist
                        (BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
                          (by
                            have hk : len ≤ lenTot := by omega
                            simpa [bw', lenTot] using
                              (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
                          (bitPos_lt_8_writeBits bw bitsTot len hbit))
                        (out.push (u8 b.toNat)) := hdecode'
                _ = some
                      (BitWriter.readerAt (BitWriter.writeBits bw bitsTot lenTot) bw'.flush
                        (by
                          simpa [bw'] using
                            (le_rfl : (BitWriter.writeBits bw bitsTot lenTot).flush.size ≤
                              (BitWriter.writeBits bw bitsTot lenTot).flush.size))
                        (bitPos_lt_8_writeBits bw bitsTot lenTot hbit),
                      byteArrayFromArray data (i + 1) (out.push (u8 b.toNat))) := hih'
                _ = some
                      (BitWriter.readerAt (BitWriter.writeBits bw bitsTot lenTot) bw'.flush
                        (by
                          simpa [bw'] using
                            (le_rfl : (BitWriter.writeBits bw bitsTot lenTot).flush.size ≤
                              (BitWriter.writeBits bw bitsTot lenTot).flush.size))
                        (bitPos_lt_8_writeBits bw bitsTot lenTot hbit),
                      byteArrayFromArray data i out) := by
                    simp [hstep]
            simpa [hbitsLen, bw', br] using hcalc
  let bitsLen := fixedLitBitsEob data i
  let bits := bitsLen.1
  let len := bitsLen.2
  let bw' := BitWriter.writeBits bw bits len
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
  have hlen_ge : data.size - i + 1 ≤ len := by
    simpa [bitsLen, len] using (fixedLitBitsEob_len_ge (data := data) (i := i))
  have hlen_le : len ≤ br.data.size * 8 := by
    have hlen_le_bitcount : len ≤ bw'.bitCount := by
      have h := Nat.le_add_left len bw.bitCount
      simpa [bw', bitCount_writeBits, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have hbitcount_le : bw'.bitCount ≤ bw'.flush.size * 8 := by
      exact flush_size_mul_ge_bitCount (bw := bw') (hbit := bw'.hbit)
    have hlen_le' : len ≤ bw'.flush.size * 8 := le_trans hlen_le_bitcount hbitcount_le
    simpa [br] using hlen_le'
  have hfuel : data.size - i + 1 ≤ br.data.size * 8 + 1 := by
    omega
  have hmain := hk (data.size - i) i bw out hbit hcur rfl (br.data.size * 8 + 1) hfuel
  unfold decodeCompressedBlock
  simpa [bitsLen, bits, len, bw', br] using hmain

end Png

end Bitmaps
