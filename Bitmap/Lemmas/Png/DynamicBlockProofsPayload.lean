import Bitmap.Lemmas.Png.DynamicBlockProofsReadTables
import Bitmap.Lemmas.Png.FixedBlockProofsCommon
import Bitmap.Lemmas.Png.FixedBlockProofsDecode
import Bitmap.Lemmas.Png.FixedLiteral

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

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
    have hrow1' :
        Array.getInternal
          (Array.getInternal fixedLitLenHuffman.table 1
            (by native_decide : 1 < fixedLitLenHuffman.table.size))
          0
          (by
            have hcode1'' :
                0 <
                  (Array.getInternal fixedLitLenHuffman.table 1
                    (by native_decide : 1 < fixedLitLenHuffman.table.size)).size := by
              native_decide
            exact hcode1'')
          = none := by
      native_decide
    simpa using hrow1'
  have hrow2 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 2 htable2) 0 hcode2 = none := by
    have hrow2' :
        Array.getInternal
          (Array.getInternal fixedLitLenHuffman.table 2
            (by native_decide : 2 < fixedLitLenHuffman.table.size))
          0
          (by
            have hcode2'' :
                0 <
                  (Array.getInternal fixedLitLenHuffman.table 2
                    (by native_decide : 2 < fixedLitLenHuffman.table.size)).size := by
              native_decide
            exact hcode2'')
          = none := by
      native_decide
    simpa using hrow2'
  have hrow3 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 3 htable3) 0 hcode3 = none := by
    have hrow3' :
        Array.getInternal
          (Array.getInternal fixedLitLenHuffman.table 3
            (by native_decide : 3 < fixedLitLenHuffman.table.size))
          0
          (by
            have hcode3'' :
                0 <
                  (Array.getInternal fixedLitLenHuffman.table 3
                    (by native_decide : 3 < fixedLitLenHuffman.table.size)).size := by
              native_decide
            exact hcode3'')
          = none := by
      native_decide
    simpa using hrow3'
  have hrow4 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 4 htable4) 0 hcode4 = none := by
    have hrow4' :
        Array.getInternal
          (Array.getInternal fixedLitLenHuffman.table 4
            (by native_decide : 4 < fixedLitLenHuffman.table.size))
          0
          (by
            have hcode4'' :
                0 <
                  (Array.getInternal fixedLitLenHuffman.table 4
                    (by native_decide : 4 < fixedLitLenHuffman.table.size)).size := by
              native_decide
            exact hcode4'')
          = none := by
      native_decide
    simpa using hrow4'
  have hrow5 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 5 htable5) 0 hcode5 = none := by
    have hrow5' :
        Array.getInternal
          (Array.getInternal fixedLitLenHuffman.table 5
            (by native_decide : 5 < fixedLitLenHuffman.table.size))
          0
          (by
            have hcode5'' :
                0 <
                  (Array.getInternal fixedLitLenHuffman.table 5
                    (by native_decide : 5 < fixedLitLenHuffman.table.size)).size := by
              native_decide
            exact hcode5'')
          = none := by
      native_decide
    simpa using hrow5'
  have hrow6 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 6 htable6) 0 hcode6 = none := by
    have hrow6' :
        Array.getInternal
          (Array.getInternal fixedLitLenHuffman.table 6
            (by native_decide : 6 < fixedLitLenHuffman.table.size))
          0
          (by
            have hcode6'' :
                0 <
                  (Array.getInternal fixedLitLenHuffman.table 6
                    (by native_decide : 6 < fixedLitLenHuffman.table.size)).size := by
              native_decide
            exact hcode6'')
          = none := by
      native_decide
    simpa using hrow6'
  have hrow7 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 7 htable7) 0 hcode7 = some 256 := by
    have hrow7' :
        Array.getInternal
          (Array.getInternal fixedLitLenHuffman.table 7
            (by native_decide : 7 < fixedLitLenHuffman.table.size))
          0
          (by
            have hcode7'' :
                0 <
                  (Array.getInternal fixedLitLenHuffman.table 7
                    (by native_decide : 7 < fixedLitLenHuffman.table.size)).size := by
              native_decide
            exact hcode7'')
          = some 256 := by
      native_decide
    simpa using hrow7'
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

end Png

end Bitmaps
