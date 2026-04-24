import Bitmap.Lemmas.Png.DynamicBlockProofsPayloadBase

universe u

namespace Bitmaps

namespace Png

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

end Png

end Bitmaps
