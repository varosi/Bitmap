import Bitmap.Lemmas.Png.DynamicBlockProofsTables

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-- Turns a bit-index bound into the byte-index bound needed by `readBit` simplifications. -/
lemma bytePos_lt_of_bitIndex_lt_dataBits (br : BitReader)
    (h : br.bitIndex < br.data.size * 8) :
    br.bytePos < br.data.size := by
  by_cases hEq : br.bytePos = br.data.size
  · have hbit0 : br.bitPos = 0 := br.hend hEq
    have hidx : br.bitIndex = br.data.size * 8 := by
      simp [BitReader.bitIndex, hEq, hbit0]
    omega
  · exact lt_of_le_of_ne br.hpos hEq

/-- Records that any well-formed reader stays within its backing byte array. -/
lemma bitIndex_le_dataBits (br : BitReader) :
    br.bitIndex ≤ br.data.size * 8 := by
  by_cases hEq : br.bytePos = br.data.size
  · have hbit0 : br.bitPos = 0 := br.hend hEq
    simp [BitReader.bitIndex, hEq, hbit0]
  · have hlt : br.bytePos < br.data.size := lt_of_le_of_ne br.hpos hEq
    have hspan : br.bitPos + 0 ≤ 8 := by
      have hbitle : br.bitPos ≤ 7 := Nat.le_of_lt_succ br.hbit
      calc
        br.bitPos + 0 = br.bitPos := by simp
        _ ≤ 7 := hbitle
        _ ≤ 8 := by decide
    simpa using readBits_within_byte_bound br 0 hspan hlt

/-- Exposes the only populated decode row of the fixed dynamic code-length Huffman table. -/
lemma dynamicCodeLenHuffman_row2_get :
    dynamicCodeLenHuffman.table[2]! = #[some 5, some 8, some 7, some 9] := by
  rfl

/-- Specializes the row-2 table lookup to the code for symbol `5`. -/
lemma dynamicCodeLenHuffman_row2_get_zero :
    dynamicCodeLenHuffman.table[2]![0] = some 5 := by
  decide

/-- Specializes the row-2 table lookup to the code for symbol `8`. -/
lemma dynamicCodeLenHuffman_row2_get_one :
    dynamicCodeLenHuffman.table[2]![1] = some 8 := by
  decide

/-- Specializes the row-2 table lookup to the code for symbol `7`. -/
lemma dynamicCodeLenHuffman_row2_get_two :
    dynamicCodeLenHuffman.table[2]![2] = some 7 := by
  decide

/-- Specializes the row-2 table lookup to the code for symbol `9`. -/
lemma dynamicCodeLenHuffman_row2_get_three :
    dynamicCodeLenHuffman.table[2]![3] = some 9 := by
  decide

/-- The low bit of `code ||| (x <<< 2)` equals `code % 2` when `code < 4`. -/
private lemma code_or_shift_two_mod_two (code x : Nat) (hcode : code < 4) :
    (code ||| (x <<< 2)) % 2 = code % 2 := by
  have hmod4 : (code ||| (x <<< 2)) % 4 = code := by
    simpa [Nat.mod_eq_of_lt hcode] using
      (mod_two_pow_or_shift (a := code) (b := x) (k := 2) (len := 2) (hk := by decide))
  have h2dvd4 : (2 : Nat) ∣ 4 := by decide
  calc
    (code ||| (x <<< 2)) % 2
        = ((code ||| (x <<< 2)) % 4) % 2 := (Nat.mod_mod_of_dvd _ h2dvd4).symm
    _ = code % 2 := by rw [hmod4]

/-- The second bit of `code ||| (x <<< 2)` equals `code / 2` when `code < 4`. -/
private lemma code_or_shift_two_shiftRight_mod_two (code x : Nat) (hcode : code < 4) :
    ((code ||| (x <<< 2)) >>> 1) % 2 = code / 2 := by
  have hmod4 : (code ||| (x <<< 2)) % 4 = code := by
    simpa [Nat.mod_eq_of_lt hcode] using
      (mod_two_pow_or_shift (a := code) (b := x) (k := 2) (len := 2) (hk := by decide))
  have hmod0 : (code ||| (x <<< 2)) % 2 = code % 2 :=
    code_or_shift_two_mod_two code x hcode
  have hdecomp := mod_two_pow_decomp_high (code ||| (x <<< 2)) 1
  rw [hmod4, hmod0] at hdecomp
  -- hdecomp : code = (code % 2) ||| ((((code ||| (x <<< 2)) >>> 1) % 2) <<< 1)
  -- The two operands are disjoint (bit 0 vs bit 1), so ||| equals +. Split on the unknown bit.
  rcases Nat.mod_two_eq_zero_or_one ((code ||| (x <<< 2)) >>> 1) with hz | ho
  · rw [hz]; simp [hz] at hdecomp; omega
  · rw [ho]; simp [ho] at hdecomp; omega

/-- Generic single-step decode for any 2-bit code (0..3) in the fixed dynamic code-length Huffman
    table. The four concrete symbols (5, 8, 7, 9) all reduce to this by picking the matching
    `code`/`sym` row lookup. -/
lemma dynamicCodeLenHuffman_decode_readerAt_writeBits_code
    (bw : BitWriter) (code sym restBits restLen : Nat)
    (hcode : code < 4)
    (hsym : dynamicCodeLenHuffman.table[2]![code] = some sym)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := code ||| (restBits <<< 2)
    let lenTot := 2 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    dynamicCodeLenHuffman.decode br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot 2) bw'.flush
          (by
            have hk : 2 ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 2 lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot 2 hbit)) := by
  let bitsTot := code ||| (restBits <<< 2)
  let lenTot := 2 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let bw1 := BitWriter.writeBit bw (bitsTot % 2)
  let br1 := BitWriter.readerAt bw1 bw'.flush
    (by
      have hk : 1 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 1 lenTot hk))
    (bitPos_lt_8_writeBit bw (bitsTot % 2) hbit)
  let br2 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 2) bw'.flush
    (by
      have hk : 2 ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 2 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 2 hbit)
  have hmod0 : bitsTot % 2 = code % 2 := code_or_shift_two_mod_two code restBits hcode
  have hmod1 : (bitsTot >>> 1) % 2 = code / 2 :=
    code_or_shift_two_shiftRight_mod_two code restBits hcode
  have hread2 :
      br.bitIndex + 2 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 2)
        (hk := by omega) hbit)
  have hbr : br.bytePos < br.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br (by omega)
  have hcur1 : bw1.curClearAbove := by
    simpa [bw1] using (curClearAbove_writeBit bw (bitsTot % 2) hbit hcur)
  have hbit1 : bw1.bitPos < 8 := by
    simpa [bw1] using (bitPos_lt_8_writeBit bw (bitsTot % 2) hbit)
  have hsplit1 :
      bw' = BitWriter.writeBits bw1 (bitsTot >>> 1) (lenTot - 1) := by
    cases restLen <;> simp [bw', bw1, lenTot, BitWriter.writeBits]
  have hread0 :
      br.readBit = (code % 2, br1) := by
    have hstep :=
      readBit_readerAt_writeBits (bw := bw) (bits := bitsTot) (len := lenTot)
        hbit hcur (by omega)
    simpa [br, bw', br1, bw1, hmod0, bitsTot, lenTot] using hstep
  have hread1Bound :
      br1.bitIndex + 1 ≤ br1.data.size * 8 := by
    simpa [br1, bw1, bw', lenTot, hsplit1] using
      (readerAt_writeBits_bound (bw := bw1) (bits := bitsTot >>> 1) (len := lenTot - 1) (k := 1)
        (hk := by omega) hbit1)
  have hbr1 : br1.bytePos < br1.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br1 (by omega)
  have hread1 :
      br1.readBit = (code / 2, br2) := by
    have hstep :=
      readBit_readerAt_writeBits (bw := bw1) (bits := bitsTot >>> 1) (len := lenTot - 1)
        hbit1 hcur1 (by omega)
    have hbw2 :
        BitWriter.writeBit bw1 (code / 2) = BitWriter.writeBits bw bitsTot 2 := by
      simp [bw1, BitWriter.writeBits, hmod0, hmod1]
    simpa [br1, bw', br2, bw1, hsplit1, hbw2, hmod1, bitsTot, lenTot] using hstep
  have hidxEq : code % 2 ||| ((code / 2) <<< 1) = code := by
    have hcases : code = 0 ∨ code = 1 ∨ code = 2 ∨ code = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;> decide
  have hlookup : [some 5, some 8, some 7, some 9][code] = some sym := by
    simpa [dynamicCodeLenHuffman] using hsym
  have hdecode :
      dynamicCodeLenHuffman.decode br = some (sym, br2) := by
    unfold Huffman.decode
    simp [Huffman.decodeFuel, dynamicCodeLenHuffman, hbr, hbr1, hread0, hread1, hidxEq, hcode]
    cases hcase : [some 5, some 8, some 7, some 9][code] with
    | none =>
        rw [hlookup] at hcase
        cases hcase
    | some val =>
        rw [hlookup] at hcase
        injection hcase with hval
        subst hval
        simp
  simpa [br2, br, bw', bitsTot, lenTot] using hdecode

/-- Packages the four concrete symbol decoders into the single case split needed downstream. -/
lemma dynamicCodeLenHuffman_decode_readerAt_writeBits
    (bw : BitWriter) (sym restBits restLen : Nat)
    (hsym : sym = 5 ∨ sym = 8 ∨ sym = 7 ∨ sym = 9)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicCodeLenSymRevBits sym ||| (restBits <<< 2)
    let lenTot := 2 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    dynamicCodeLenHuffman.decode br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot 2) bw'.flush
          (by
            have hk : 2 ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 2 lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot 2 hbit)) := by
  rcases hsym with rfl | rfl | rfl | rfl
  · simpa [dynamicCodeLenSymRevBits] using
      dynamicCodeLenHuffman_decode_readerAt_writeBits_code
        (bw := bw) (code := 0) (sym := 5) (restBits := restBits) (restLen := restLen)
        (by decide) dynamicCodeLenHuffman_row2_get_zero hbit hcur
  · simpa [dynamicCodeLenSymRevBits] using
      dynamicCodeLenHuffman_decode_readerAt_writeBits_code
        (bw := bw) (code := 1) (sym := 8) (restBits := restBits) (restLen := restLen)
        (by decide) dynamicCodeLenHuffman_row2_get_one hbit hcur
  · simpa [dynamicCodeLenSymRevBits] using
      dynamicCodeLenHuffman_decode_readerAt_writeBits_code
        (bw := bw) (code := 2) (sym := 7) (restBits := restBits) (restLen := restLen)
        (by decide) dynamicCodeLenHuffman_row2_get_two hbit hcur
  · simpa [dynamicCodeLenSymRevBits] using
      dynamicCodeLenHuffman_decode_readerAt_writeBits_code
        (bw := bw) (code := 3) (sym := 9) (restBits := restBits) (restLen := restLen)
        (by decide) dynamicCodeLenHuffman_row2_get_three hbit hcur

def pushNatList (lengths : Array Nat) : List Nat → Array Nat
  | [] => lengths
  | sym :: syms => pushNatList (lengths.push sym) syms

set_option maxRecDepth 200000 in
/-- Unfolds one literal step of the code-length reader once the Huffman decode result is known. -/
lemma readDynamicTablesLengthsFuel_step_literal
    (fuel total sym : Nat) (br br' : BitReader) (lengths : Array Nat)
    (hsize : lengths.size < total)
    (hdecode : dynamicCodeLenHuffman.decode br = some (sym, br'))
    (hsym : sym ≤ 15) :
    readDynamicTablesLengthsFuel (fuel + 1) total dynamicCodeLenHuffman br lengths =
      readDynamicTablesLengthsFuel fuel total dynamicCodeLenHuffman br' (lengths.push sym) := by
  have hge : ¬ total ≤ lengths.size := Nat.not_le_of_lt hsize
  simp [readDynamicTablesLengthsFuel, hge, hdecode, hsym]

private lemma readerAt_eq_of_eqs
    {bw1 bw2 : BitWriter} {data1 data2 : ByteArray}
    (hbw : bw1 = bw2) (hdata : data1 = data2)
    (hflush1 : bw1.flush.size ≤ data1.size) (hflush2 : bw2.flush.size ≤ data2.size)
    (hbit1 : bw1.bitPos < 8) (hbit2 : bw2.bitPos < 8) :
    BitWriter.readerAt bw1 data1 hflush1 hbit1 =
      BitWriter.readerAt bw2 data2 hflush2 hbit2 := by
  subst hbw
  subst hdata
  apply BitReader.ext <;> simp [BitWriter.readerAt]

/-- Replays a whole list of concrete code-length symbols against `readDynamicTablesLengthsFuel`. -/
lemma readDynamicTablesLengthsFuel_dynamicCodeLenSymBits_readerAt_writeBits
    (bw : BitWriter) (syms : List Nat) (fuel restBits restLen : Nat) (lengths : Array Nat)
    (hsyms : ∀ sym ∈ syms, sym = 5 ∨ sym = 8 ∨ sym = 7 ∨ sym = 9)
    (hfuel : syms.length + 1 ≤ fuel)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length))
    let lenTot := 2 * syms.length + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    readDynamicTablesLengthsFuel fuel (lengths.size + syms.length) dynamicCodeLenHuffman br lengths =
      some
        (pushNatList lengths syms,
          BitWriter.readerAt (BitWriter.writeBits bw bitsTot (2 * syms.length)) bw'.flush
            (by
              have hk : 2 * syms.length ≤ lenTot := by omega
              simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot (2 * syms.length) lenTot hk))
            (bitPos_lt_8_writeBits bw bitsTot (2 * syms.length) hbit)) := by
  induction syms generalizing bw fuel restBits restLen lengths with
  | nil =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero 0 hfuel)
      | succ fuel =>
          simp [pushNatList, dynamicCodeLenSymBits, readDynamicTablesLengthsFuel]
  | cons sym syms ih =>
      cases fuel with
      | zero =>
          cases (Nat.not_succ_le_zero _ hfuel)
      | succ fuel =>
      let restBits1 := dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length))
      let restLen1 := 2 * syms.length + restLen
      let bitsTot := dynamicCodeLenSymRevBits sym ||| (restBits1 <<< 2)
      let lenTot := 2 + restLen1
      have hsym : sym = 5 ∨ sym = 8 ∨ sym = 7 ∨ sym = 9 := by
        exact hsyms sym (by simp)
      have hsymsTail : ∀ s ∈ syms, s = 5 ∨ s = 8 ∨ s = 7 ∨ s = 9 := by
        intro s hs
        exact hsyms s (by simp [hs])
      have hfuelTail : syms.length + 1 ≤ fuel := by
        exact Nat.succ_le_succ_iff.mp (by simpa [Nat.add_assoc] using hfuel)
      have hsymLe : sym ≤ 15 := by
        rcases hsym with rfl | rfl | rfl | rfl <;> decide
      have hsymBitsLt : dynamicCodeLenSymRevBits sym < 2 ^ 2 := by
        rcases hsym with rfl | rfl | rfl | rfl <;> simp [dynamicCodeLenSymRevBits]
      have hdecode :
          let bw' := BitWriter.writeBits bw bitsTot lenTot
          let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
          dynamicCodeLenHuffman.decode br =
            some
              (sym,
                BitWriter.readerAt (BitWriter.writeBits bw bitsTot 2) bw'.flush
                  (by
                    have hk : 2 ≤ lenTot := by omega
                    simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 2 lenTot hk))
                  (bitPos_lt_8_writeBits bw bitsTot 2 hbit)) := by
        exact
          dynamicCodeLenHuffman_decode_readerAt_writeBits
            (bw := bw) (sym := sym) (restBits := restBits1) (restLen := restLen1) hsym hbit hcur
      have hprefixMod :
          bitsTot % 2 ^ 2 = dynamicCodeLenSymRevBits sym := by
        have hmod :=
          mod_two_pow_or_shift
            (a := dynamicCodeLenSymRevBits sym) (b := restBits1) (k := 2) (len := 2) (hk := by decide)
        have hmodSym :
            dynamicCodeLenSymRevBits sym % 2 ^ 2 = dynamicCodeLenSymRevBits sym :=
          Nat.mod_eq_of_lt hsymBitsLt
        simpa [bitsTot, hmodSym] using hmod
      have hprefixWriter :
          BitWriter.writeBits bw bitsTot 2 =
            BitWriter.writeBits bw (dynamicCodeLenSymRevBits sym) 2 := by
        rw [writeBits_mod, hprefixMod]
      have hconcatTotal :
          BitWriter.writeBits bw bitsTot lenTot =
            BitWriter.writeBits (BitWriter.writeBits bw (dynamicCodeLenSymRevBits sym) 2) restBits1 restLen1 := by
        simpa [bitsTot, lenTot, restLen1, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (writeBits_concat bw (dynamicCodeLenSymRevBits sym) restBits1 2 restLen1 hsymBitsLt)
      have hconcatConsumed :
          BitWriter.writeBits bw bitsTot (2 * List.length (sym :: syms)) =
            BitWriter.writeBits (BitWriter.writeBits bw (dynamicCodeLenSymRevBits sym) 2)
              (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
              (2 * syms.length) := by
        simpa [bitsTot, restBits1, Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (writeBits_concat bw (dynamicCodeLenSymRevBits sym)
            (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length))) 2 (2 * syms.length) hsymBitsLt)
      have hconcatTotal' :
          BitWriter.writeBits bw bitsTot lenTot =
            BitWriter.writeBits (BitWriter.writeBits bw bitsTot 2) restBits1 restLen1 := by
        rw [hprefixWriter]
        exact hconcatTotal
      have htail :
          let bwTail := BitWriter.writeBits bw bitsTot 2
          let bwTail' := BitWriter.writeBits bwTail
            (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
            (2 * syms.length + restLen)
          let brTail := BitWriter.readerAt bwTail bwTail'.flush
            (flush_size_writeBits_le bwTail
              (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
              (2 * syms.length + restLen))
            (bitPos_lt_8_writeBits bw bitsTot 2 hbit)
          readDynamicTablesLengthsFuel fuel
              ((lengths.push sym).size + syms.length) dynamicCodeLenHuffman brTail (lengths.push sym) =
            some
              (pushNatList (lengths.push sym) syms,
                BitWriter.readerAt
                  (BitWriter.writeBits bwTail
                    (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
                    (2 * syms.length))
                  bwTail'.flush
                  (by
                    have hk : 2 * syms.length ≤ 2 * syms.length + restLen := by omega
                    simpa using
                      (flush_size_writeBits_prefix bwTail
                        (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
                        (2 * syms.length) (2 * syms.length + restLen) hk))
                  (bitPos_lt_8_writeBits bwTail
                    (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
                    (2 * syms.length)
                    (bitPos_lt_8_writeBits bw bitsTot 2 hbit))) := by
        simpa using
          (ih (bw := BitWriter.writeBits bw bitsTot 2) (fuel := fuel) (restBits := restBits)
            (restLen := restLen) (lengths := lengths.push sym) hsymsTail hfuelTail
            (bitPos_lt_8_writeBits bw bitsTot 2 hbit)
            (curClearAbove_writeBits bw bitsTot 2 hbit hcur))
      have hsizeFalse : ¬ lengths.size ≥ lengths.size + List.length (sym :: syms) := by
        simp
      let bwFull := BitWriter.writeBits bw bitsTot lenTot
      let brStart := BitWriter.readerAt bw bwFull.flush
        (flush_size_writeBits_le bw bitsTot lenTot) hbit
      let brNext := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 2) bwFull.flush
        (by
          have hk : 2 ≤ lenTot := by omega
          simpa [bwFull, lenTot] using (flush_size_writeBits_prefix bw bitsTot 2 lenTot hk))
        (bitPos_lt_8_writeBits bw bitsTot 2 hbit)
      have hstep :
          readDynamicTablesLengthsFuel (fuel + 1) (lengths.size + List.length (sym :: syms))
            dynamicCodeLenHuffman brStart lengths =
            readDynamicTablesLengthsFuel fuel ((lengths.push sym).size + syms.length)
              dynamicCodeLenHuffman brNext (lengths.push sym) := by
        have hsize' : lengths.size < lengths.size + List.length (sym :: syms) := by
          simp
        simpa [Array.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (readDynamicTablesLengthsFuel_step_literal
            (fuel := fuel) (total := lengths.size + List.length (sym :: syms))
            (sym := sym) (br := brStart) (br' := brNext) (lengths := lengths)
            hsize' (by simpa [bwFull, brStart, brNext] using hdecode) hsymLe)
      have hafterWriter :
          BitWriter.writeBits
              (BitWriter.writeBits bw bitsTot 2)
              (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
              (2 * syms.length) =
            BitWriter.writeBits bw bitsTot (2 * List.length (sym :: syms)) := by
        rw [hprefixWriter]
        simpa [bitsTot, restBits1, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hconcatConsumed.symm
      have hfullFlush :
          (BitWriter.writeBits
              (BitWriter.writeBits bw bitsTot 2)
              (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
              (2 * syms.length + restLen)).flush =
            bwFull.flush := by
        simpa [bwFull] using congrArg BitWriter.flush hconcatTotal'.symm
      have hbrNextEq :
          BitWriter.readerAt
            (BitWriter.writeBits bw bitsTot 2)
            ((BitWriter.writeBits
                (BitWriter.writeBits bw bitsTot 2)
                (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
                (2 * syms.length + restLen)).flush)
            (by
              simpa [hfullFlush, bwFull] using
                (flush_size_writeBits_le
                  (BitWriter.writeBits bw bitsTot 2)
                  (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
                  (2 * syms.length + restLen)))
            (bitPos_lt_8_writeBits bw bitsTot 2 hbit) =
          brNext := by
        refine readerAt_eq_of_eqs rfl hfullFlush _ _ _ _
      have hafterReader :
          BitWriter.readerAt
              (BitWriter.writeBits
                (BitWriter.writeBits bw bitsTot 2)
                (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
                (2 * syms.length))
              ((BitWriter.writeBits
                  (BitWriter.writeBits bw bitsTot 2)
                  (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
                  (2 * syms.length + restLen)).flush)
              (by
                have hk : 2 * syms.length ≤ 2 * syms.length + restLen := by omega
                simpa using
                  (flush_size_writeBits_prefix
                    (BitWriter.writeBits bw bitsTot 2)
                    (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
                    (2 * syms.length) (2 * syms.length + restLen) hk))
              (bitPos_lt_8_writeBits
                (BitWriter.writeBits bw bitsTot 2)
                (dynamicCodeLenSymBits syms ||| (restBits <<< (2 * syms.length)))
                (2 * syms.length)
                (bitPos_lt_8_writeBits bw bitsTot 2 hbit)) =
            BitWriter.readerAt
              (BitWriter.writeBits bw bitsTot (2 * List.length (sym :: syms)))
              bwFull.flush
              (by
                have hk : 2 * List.length (sym :: syms) ≤ lenTot := by
                  dsimp [lenTot, restLen1]
                  omega
                simpa [bwFull, lenTot] using
                  (flush_size_writeBits_prefix bw bitsTot (2 * List.length (sym :: syms)) lenTot hk))
              (bitPos_lt_8_writeBits bw bitsTot (2 * List.length (sym :: syms)) hbit) := by
        refine readerAt_eq_of_eqs hafterWriter hfullFlush _ _ _ _
      have hfinish :
          readDynamicTablesLengthsFuel fuel ((lengths.push sym).size + syms.length)
            dynamicCodeLenHuffman brNext (lengths.push sym) =
          some
            (pushNatList (lengths.push sym) syms,
              BitWriter.readerAt
                (BitWriter.writeBits bw bitsTot (2 * List.length (sym :: syms)))
                bwFull.flush
                (by
                  have hk : 2 * List.length (sym :: syms) ≤ lenTot := by
                    dsimp [lenTot, restLen1]
                    omega
                  simpa [bwFull, lenTot] using
                    (flush_size_writeBits_prefix bw bitsTot (2 * List.length (sym :: syms)) lenTot hk))
                (bitPos_lt_8_writeBits bw bitsTot (2 * List.length (sym :: syms)) hbit)) := by
        simpa [brNext, bwFull, hafterWriter, hfullFlush] using htail
      have hmain :
          readDynamicTablesLengthsFuel (fuel + 1) (lengths.size + List.length (sym :: syms))
            dynamicCodeLenHuffman brStart lengths =
          some
            (pushNatList (lengths.push sym) syms,
              BitWriter.readerAt
                (BitWriter.writeBits bw bitsTot (2 * List.length (sym :: syms)))
                bwFull.flush
                (by
                  have hk : 2 * List.length (sym :: syms) ≤ lenTot := by
                    dsimp [lenTot, restLen1]
                    omega
                  simpa [bwFull, lenTot] using
                    (flush_size_writeBits_prefix bw bitsTot (2 * List.length (sym :: syms)) lenTot hk))
                (bitPos_lt_8_writeBits bw bitsTot (2 * List.length (sym :: syms)) hbit)) := by
        exact hstep.trans hfinish
      have hlenShift : 2 * List.length (sym :: syms) = 2 * syms.length + 2 := by
        simpa using (show 2 * (syms.length + 1) = 2 * syms.length + 2 by omega)
      have hbitsTotNorm :
          bitsTot =
            dynamicCodeLenSymBits (sym :: syms) ||| (restBits <<< (2 * List.length (sym :: syms))) := by
        have hshiftRest :
            (restBits <<< (2 * syms.length)) <<< 2 =
              restBits <<< (2 * List.length (sym :: syms)) := by
          rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, hlenShift, Nat.pow_add]
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        dsimp [bitsTot, restBits1]
        rw [(Nat.shiftLeft_or_distrib (a := dynamicCodeLenSymBits syms)
          (b := restBits <<< (2 * syms.length)) (i := 2)), hshiftRest]
        rw [dynamicCodeLenSymBits, Nat.or_assoc]
        rw [show 2 * List.length (sym :: syms) = 2 * (syms.length + 1) by simp]
      have hlenTotNorm : lenTot = 2 * List.length (sym :: syms) + restLen := by
        dsimp [lenTot, restLen1]
        omega
      simpa [bwFull, brStart, pushNatList, hbitsTotNorm, hlenTotNorm] using hmain

set_option maxRecDepth 200000 in
/-- Evaluates the concrete code-length symbol list into the final lit/len and distance lengths arrays. -/
lemma pushNatList_empty_dynamicHeaderCodeLenSyms :
    pushNatList #[] dynamicHeaderCodeLenSyms =
      dynamicLitLenLengths ++ dynamicDistLengths := by
  native_decide

set_option maxRecDepth 200000 in
/-- Runs the code-length reader over the encoder's exact ten-symbol code-length stream. -/
lemma readDynamicTablesLengthsFuel_dynamicHeaderCodeLenSyms_readerAt_writeBits
    (bw : BitWriter) (fuel restBits restLen : Nat)
    (hfuel : dynamicHeaderCodeLenSyms.length + 1 ≤ fuel)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicCodeLenSymBits dynamicHeaderCodeLenSyms |||
      (restBits <<< (2 * dynamicHeaderCodeLenSyms.length))
    let lenTot := 2 * dynamicHeaderCodeLenSyms.length + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    readDynamicTablesLengthsFuel fuel
      ((dynamicLitLenLengths ++ dynamicDistLengths).size) dynamicCodeLenHuffman br #[] =
      some
        (dynamicLitLenLengths ++ dynamicDistLengths,
          BitWriter.readerAt
            (BitWriter.writeBits bw bitsTot (2 * dynamicHeaderCodeLenSyms.length))
            bw'.flush
            (by
              have hk : 2 * dynamicHeaderCodeLenSyms.length ≤ lenTot := by omega
              simpa [lenTot] using
                (flush_size_writeBits_prefix bw bitsTot (2 * dynamicHeaderCodeLenSyms.length) lenTot hk))
            (bitPos_lt_8_writeBits bw bitsTot (2 * dynamicHeaderCodeLenSyms.length) hbit)) := by
  have hsyms :
      ∀ sym ∈ dynamicHeaderCodeLenSyms, sym = 5 ∨ sym = 8 ∨ sym = 7 ∨ sym = 9 := by
    native_decide
  have hmain :=
    readDynamicTablesLengthsFuel_dynamicCodeLenSymBits_readerAt_writeBits
      (bw := bw) (syms := dynamicHeaderCodeLenSyms) (fuel := fuel)
      (restBits := restBits) (restLen := restLen) (lengths := #[])
      hsyms hfuel hbit hcur
  rw [pushNatList_empty_dynamicHeaderCodeLenSyms] at hmain
  exact hmain

end Png

end Bitmaps
