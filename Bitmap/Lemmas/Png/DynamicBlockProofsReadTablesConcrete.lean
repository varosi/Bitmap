import Bitmap.Lemmas.Png.DynamicBlockProofsReadTablesHeaderReads
import Bitmap.Lemmas.Png.DynamicBlockProofsReadTables

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Restates the full table-read theorem in the concrete front-end shape of `readDynamicTables`. -/
lemma readDynamicTables_readerAt_writeBits_concrete
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderReadBits restBits
    let lenTot := dynamicHeaderReadLen restLen
    let bwFull := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bwFull.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    readDynamicTables br =
      some
        (fixedLitLenHuffman, fixedDistHuffman,
          dynamicTablesAfterHeaderReaderAt
            (BitWriter.writeBits bw bitsTot 14) restBits restLen
            (bitPos_lt_8_writeBits bw bitsTot 14 hbit)) := by
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bwFull := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bwFull.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br5 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 5) bwFull.flush
    (by
      have hk : 5 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
      simpa [bwFull, lenTot] using flush_size_writeBits_prefix bw bitsTot 5 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  let br10 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 10) bwFull.flush
    (by
      have hk : 10 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
      simpa [bwFull, lenTot] using flush_size_writeBits_prefix bw bitsTot 10 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 10 hbit)
  let bw14 := BitWriter.writeBits bw bitsTot 14
  let br14 := BitWriter.readerAt bw14 bwFull.flush
    (by
      have hk : 14 ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderReadLen_ge_14 restLen
      simpa [bwFull, lenTot] using flush_size_writeBits_prefix bw bitsTot 14 lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot 14 hbit)
  have hreadHlit := by
    simpa [bitsTot, lenTot, bwFull, br, br5] using
      (readDynamicTables_hlit_readerAt_writeBits
        (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur)
  have hreadHdist := by
    simpa [bitsTot, lenTot, bwFull, br5, br10] using
      (readDynamicTables_hdist_readerAt_writeBits
        (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur)
  have hreadHclen := by
    simpa [bitsTot, lenTot, bwFull, bw14, br10, br14] using
      (readDynamicTables_hclen_readerAt_writeBits
        (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur)
  have hbit14 : bw14.bitPos < 8 := by
    simpa [bw14] using bitPos_lt_8_writeBits bw bitsTot 14 hbit
  have hcur14 : bw14.curClearAbove := by
    simpa [bw14] using curClearAbove_writeBits bw bitsTot 14 hbit hcur
  have hbw14Full :
      bwFull =
        BitWriter.writeBits bw14 (dynamicHeaderCodeLenLensBits restBits)
          (dynamicHeaderCodeLenLensLen restLen) := by
    have hk14 : 14 ≤ lenTot := by
      simpa [lenTot] using dynamicHeaderReadLen_ge_14 restLen
    have hshift14 : bitsTot >>> 14 = dynamicHeaderCodeLenLensBits restBits := by
      simpa [bitsTot] using dynamicHeaderReadBits_shift14 restBits
    have hlen14 : lenTot - 14 = dynamicHeaderCodeLenLensLen restLen := by
      simpa [lenTot] using dynamicHeaderReadLen_sub14 restLen
    calc
      bwFull = BitWriter.writeBits bw bitsTot (14 + (lenTot - 14)) := by
        simp [bwFull, Nat.add_sub_of_le hk14]
      _ = BitWriter.writeBits (BitWriter.writeBits bw bitsTot 14) (bitsTot >>> 14) (lenTot - 14) := by
        simpa using writeBits_split bw bitsTot 14 (lenTot - 14)
      _ = BitWriter.writeBits bw14 (dynamicHeaderCodeLenLensBits restBits)
            (dynamicHeaderCodeLenLensLen restLen) := by
        rw [hshift14, hlen14]
  have hfull14Flush :
      (BitWriter.writeBits bw14 (dynamicHeaderCodeLenLensBits restBits)
        (dynamicHeaderCodeLenLensLen restLen)).flush = bwFull.flush := by
    simpa [bwFull] using congrArg BitWriter.flush hbw14Full.symm
  have hafterHeader0 :=
    readDynamicTablesAfterHeader_readerAt_writeBits
      (bw := bw14) (restBits := restBits) (restLen := restLen) hbit14 hcur14
  have hafterHeader :
      readDynamicTablesAfterHeader br14 =
        some
          (fixedLitLenHuffman, fixedDistHuffman,
            dynamicTablesAfterHeaderReaderAt bw14 restBits restLen hbit14) := by
    simpa [br14, hfull14Flush] using hafterHeader0
  have hcondHlit : br.bitIndex + 5 ≤ br.data.size * 8 := by
    have hk : 5 ≤ lenTot := by
      simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
    simpa [br, bwFull, lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 5) hk hbit)
  have hcondHdist : br5.bitIndex + 5 ≤ br5.data.size * 8 := by
    have hk : 5 ≤ lenTot - 5 := by
      simpa [lenTot] using dynamicHeaderReadLen_sub5_ge_5 restLen
    let bw5 := BitWriter.writeBits bw bitsTot 5
    let bwRest5 := BitWriter.writeBits bw5 (bitsTot >>> 5) (lenTot - 5)
    have hflush5 : bwRest5.flush = bwFull.flush := by
      calc
        bwRest5.flush =
            (BitWriter.writeBits
              (BitWriter.writeBits bw bitsTot 5)
              (bitsTot >>> 5)
              (lenTot - 5)).flush := by
                simp [bw5, bwRest5]
        _ = bwFull.flush := by
            have hsplit :
                bwFull =
                  BitWriter.writeBits
                    (BitWriter.writeBits bw bitsTot 5)
                    (bitsTot >>> 5)
                    (lenTot - 5) := by
                  have hk5 : 5 ≤ lenTot := by
                    simpa [lenTot] using dynamicHeaderReadLen_ge_5 restLen
                  calc
                    bwFull = BitWriter.writeBits bw bitsTot (5 + (lenTot - 5)) := by
                      simp [bwFull, Nat.add_sub_of_le hk5]
                    _ =
                        BitWriter.writeBits
                          (BitWriter.writeBits bw bitsTot 5)
                          (bitsTot >>> 5)
                          (lenTot - 5) := by
                            simpa using writeBits_split bw bitsTot 5 (lenTot - 5)
            simpa [bwFull] using congrArg BitWriter.flush hsplit.symm
    have hreader5 :
        BitWriter.readerAt bw5 bwRest5.flush
            (flush_size_writeBits_le bw5 (bitsTot >>> 5) (lenTot - 5))
            (bitPos_lt_8_writeBits bw bitsTot 5 hbit) = br5 := by
      apply readerAt_eq_of_eqs (hbw := rfl) (hdata := hflush5)
    have hboundSplit :
        (BitWriter.readerAt bw5 bwRest5.flush
            (flush_size_writeBits_le bw5 (bitsTot >>> 5) (lenTot - 5))
            (bitPos_lt_8_writeBits bw bitsTot 5 hbit)).bitIndex + 5 ≤
          (BitWriter.readerAt bw5 bwRest5.flush
            (flush_size_writeBits_le bw5 (bitsTot >>> 5) (lenTot - 5))
            (bitPos_lt_8_writeBits bw bitsTot 5 hbit)).data.size * 8 := by
      simpa [bw5, bwRest5] using
        (readerAt_writeBits_bound
          (bw := BitWriter.writeBits bw bitsTot 5) (bits := bitsTot >>> 5) (len := lenTot - 5)
          (k := 5) hk (bitPos_lt_8_writeBits bw bitsTot 5 hbit))
    rw [← hreader5]
    exact hboundSplit
  have hcondHclen : br10.bitIndex + 4 ≤ br10.data.size * 8 := by
    have hk : 4 ≤ lenTot - 10 := by
      simpa [lenTot] using dynamicHeaderReadLen_sub10_ge_4 restLen
    let bw10 := BitWriter.writeBits bw bitsTot 10
    let bwRest10 := BitWriter.writeBits bw10 (bitsTot >>> 10) (lenTot - 10)
    have hflush10 : bwRest10.flush = bwFull.flush := by
      calc
        bwRest10.flush =
            (BitWriter.writeBits
              (BitWriter.writeBits bw bitsTot 10)
              (bitsTot >>> 10)
              (lenTot - 10)).flush := by
                simp [bw10, bwRest10]
        _ = bwFull.flush := by
            have hsplit :
                bwFull =
                  BitWriter.writeBits
                    (BitWriter.writeBits bw bitsTot 10)
                    (bitsTot >>> 10)
                    (lenTot - 10) := by
                  have hk10 : 10 ≤ lenTot := by
                    simpa [lenTot] using dynamicHeaderReadLen_ge_10 restLen
                  calc
                    bwFull = BitWriter.writeBits bw bitsTot (10 + (lenTot - 10)) := by
                      simp [bwFull, Nat.add_sub_of_le hk10]
                    _ =
                        BitWriter.writeBits
                          (BitWriter.writeBits bw bitsTot 10)
                          (bitsTot >>> 10)
                          (lenTot - 10) := by
                            simpa using writeBits_split bw bitsTot 10 (lenTot - 10)
            simpa [bwFull] using congrArg BitWriter.flush hsplit.symm
    have hreader10 :
        BitWriter.readerAt bw10 bwRest10.flush
            (flush_size_writeBits_le bw10 (bitsTot >>> 10) (lenTot - 10))
            (bitPos_lt_8_writeBits bw bitsTot 10 hbit) = br10 := by
      apply readerAt_eq_of_eqs (hbw := rfl) (hdata := hflush10)
    have hboundSplit :
        (BitWriter.readerAt bw10 bwRest10.flush
            (flush_size_writeBits_le bw10 (bitsTot >>> 10) (lenTot - 10))
            (bitPos_lt_8_writeBits bw bitsTot 10 hbit)).bitIndex + 4 ≤
          (BitWriter.readerAt bw10 bwRest10.flush
            (flush_size_writeBits_le bw10 (bitsTot >>> 10) (lenTot - 10))
            (bitPos_lt_8_writeBits bw bitsTot 10 hbit)).data.size * 8 := by
      simpa [bw10, bwRest10] using
        (readerAt_writeBits_bound
          (bw := BitWriter.writeBits bw bitsTot 10) (bits := bitsTot >>> 10) (len := lenTot - 10)
          (k := 4) hk (bitPos_lt_8_writeBits bw bitsTot 10 hbit))
    rw [← hreader10]
    exact hboundSplit
  have hmain :
      readDynamicTables br =
        some
          (fixedLitLenHuffman, fixedDistHuffman,
            dynamicTablesAfterHeaderReaderAt bw14 restBits restLen hbit14) := by
    unfold readDynamicTables
    simp [hcondHlit]
    rw [hreadHlit]
    refine ⟨hcondHdist, ?_⟩
    rw [hreadHdist]
    refine ⟨hcondHclen, ?_⟩
    rw [hreadHclen]
    simp
    have hloop :
        forIn (List.range' 0 10)
            ((⟨br14, Array.replicate 19 0⟩ : MProd BitReader (Array Nat)))
            (fun i r =>
              if h : r.fst.bitIndex + 3 ≤ r.fst.data.size * 8 then
                some
                  (ForInStep.yield
                    ⟨(r.fst.readBits 3 h).snd,
                      r.snd.setIfInBounds
                        ([16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15][i]?.getD 0)
                        (r.fst.readBits 3 h).fst⟩)
              else
                none) =
          ((fun r : Array Nat × BitReader => (⟨r.snd, r.fst⟩ : MProd BitReader (Array Nat))) <$>
            readDynamicCodeLenLengths10 br14) := by
      simpa using (readDynamicCodeLenLengths10_eq_forIn_range10_mprod br14)
    let tail : Array Nat × BitReader → Option (Huffman × Huffman × BitReader) :=
      fun (r : Array Nat × BitReader) =>
      (mkHuffman r.fst).bind fun codeLenTable =>
        (readDynamicTablesLengthsFuel (r.snd.data.size * 8 + 1) 320 codeLenTable r.snd #[]).bind
          fun __discr =>
            if __discr.fst.size = 320 then
              (mkHuffman (__discr.fst.extract 0 288)).bind fun litLenTable =>
                (buildDynamicDistTable (__discr.fst.extract 288 320)).bind fun distTable =>
                  some (litLenTable, distTable, __discr.snd)
            else
              none
    let tailM : MProd BitReader (Array Nat) → Option (Huffman × Huffman × BitReader) :=
      fun r => tail (r.snd, r.fst)
    have hloopBind0 := by
      simpa [tailM, Option.map] using congrArg (fun x => x.bind tailM) hloop
    have hswapBind :
        ((((fun r : Array Nat × BitReader => (⟨r.snd, r.fst⟩ : MProd BitReader (Array Nat))) <$>
            readDynamicCodeLenLengths10 br14)).bind tailM) =
          (readDynamicCodeLenLengths10 br14).bind tail := by
      cases hread : readDynamicCodeLenLengths10 br14 <;> simp [tailM, tail]
    have hloopBind := hloopBind0.trans hswapBind
    have hafter :
        (readDynamicCodeLenLengths10 br14).bind tail =
          some
            (fixedLitLenHuffman, fixedDistHuffman,
              dynamicTablesAfterHeaderReaderAt bw14 restBits restLen hbit14) := by
      simpa [tail, readDynamicTablesAfterHeader] using hafterHeader
    simpa [tailM, tail, bitsTot, lenTot, bwFull, bw14, br14, readBits_proof_irrel] using
      hloopBind.trans hafter
  simpa [br, bwFull, bitsTot, lenTot, bw14] using hmain

end Png

end Bitmaps
