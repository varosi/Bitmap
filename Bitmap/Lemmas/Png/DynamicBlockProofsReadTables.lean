import Bitmap.Lemmas.Png.DynamicBlockProofsDecode
import Batteries.Data.List.Lemmas
import Batteries.Control.ForInStep.Lemmas

namespace Bitmaps

namespace Png

def fixedWidthListBits (width : Nat) : List Nat → Nat
  | [] => 0
  | n :: ns => n ||| (fixedWidthListBits width ns <<< width)

def dynamicHeaderCodeLenSymsRestBits (restBits : Nat) : Nat :=
  dynamicCodeLenSymBits dynamicHeaderCodeLenSyms |||
    (restBits <<< (2 * dynamicHeaderCodeLenSyms.length))

def dynamicHeaderCodeLenSymsRestLen (restLen : Nat) : Nat :=
  2 * dynamicHeaderCodeLenSyms.length + restLen

def dynamicHeaderCodeLenLensBits (restBits : Nat) : Nat :=
  fixedWidthListBits 3 dynamicHeaderCodeLenLens |||
    (dynamicHeaderCodeLenSymsRestBits restBits <<< (3 * dynamicHeaderCodeLenLens.length))

def dynamicHeaderCodeLenLensLen (restLen : Nat) : Nat :=
  3 * dynamicHeaderCodeLenLens.length + dynamicHeaderCodeLenSymsRestLen restLen

def dynamicHeaderReadBits (restBits : Nat) : Nat :=
  let bitsHclen := 6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4)
  let bitsHdist := 31 ||| (bitsHclen <<< 5)
  31 ||| (bitsHdist <<< 5)

def dynamicHeaderReadLen (restLen : Nat) : Nat :=
  5 + 5 + 4 + dynamicHeaderCodeLenLensLen restLen

private def read3Bits? (br : BitReader) : Option (Nat × BitReader) :=
  if h : br.bitIndex + 3 ≤ br.data.size * 8 then
    some (br.readBits 3 h)
  else
    none

def readDynamicCodeLenLengthsHead5 (br : BitReader) : Option (Array Nat × BitReader) := do
  let codeLenLengths : Array Nat := Array.replicate 19 0
  let (len16, br) ← read3Bits? br
  let codeLenLengths := codeLenLengths.set! 16 len16
  let (len17, br) ← read3Bits? br
  let codeLenLengths := codeLenLengths.set! 17 len17
  let (len18, br) ← read3Bits? br
  let codeLenLengths := codeLenLengths.set! 18 len18
  let (len0, br) ← read3Bits? br
  let codeLenLengths := codeLenLengths.set! 0 len0
  let (len8, br) ← read3Bits? br
  let codeLenLengths := codeLenLengths.set! 8 len8
  return (codeLenLengths, br)

def readDynamicCodeLenLengthsTail5 (codeLenLengths : Array Nat) (br : BitReader) :
    Option (Array Nat × BitReader) := do
  let (len7, br) ← read3Bits? br
  let codeLenLengths := codeLenLengths.set! 7 len7
  let (len9, br) ← read3Bits? br
  let codeLenLengths := codeLenLengths.set! 9 len9
  let (len6, br) ← read3Bits? br
  let codeLenLengths := codeLenLengths.set! 6 len6
  let (len10, br) ← read3Bits? br
  let codeLenLengths := codeLenLengths.set! 10 len10
  let (len5, br) ← read3Bits? br
  let codeLenLengths := codeLenLengths.set! 5 len5
  return (codeLenLengths, br)

def readDynamicCodeLenLengths10 (br : BitReader) : Option (Array Nat × BitReader) := do
  let (codeLenLengths, br) ← readDynamicCodeLenLengthsHead5 br
  readDynamicCodeLenLengthsTail5 codeLenLengths br

private def dynamicCodeLenLoopBody (i : Nat) (r : BitReader × Array Nat) :
    Option (ForInStep (BitReader × Array Nat)) :=
  if h : r.fst.bitIndex + 3 ≤ r.fst.data.size * 8 then
    some
      (ForInStep.yield
        ⟨(r.fst.readBits 3 h).snd,
          r.snd.setIfInBounds
            ([16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15][i]?.getD 0)
            (r.fst.readBits 3 h).fst⟩)
  else
    none

private def dynamicCodeLenLoopBodyM (i : Nat) (r : MProd BitReader (Array Nat)) :
    Option (ForInStep (MProd BitReader (Array Nat))) :=
  if h : r.fst.bitIndex + 3 ≤ r.fst.data.size * 8 then
    some
      (ForInStep.yield
        ⟨(r.fst.readBits 3 h).snd,
          r.snd.setIfInBounds
            ([16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15][i]?.getD 0)
            (r.fst.readBits 3 h).fst⟩)
  else
    none

private lemma bindList_range0_5_eq_head5 (br : BitReader) :
    (ForInStep.yield ((br, Array.replicate 19 0) : BitReader × Array Nat)).bindList
        dynamicCodeLenLoopBody (List.range' 0 5) =
      (ForInStep.yield <$> (Prod.swap <$> readDynamicCodeLenLengthsHead5 br)) := by
  unfold readDynamicCodeLenLengthsHead5 read3Bits?
  simp [dynamicCodeLenLoopBody, List.range', Option.map]
  repeat' (first | split <;> simp_all)

private lemma bindList_range5_5_eq_tail5 (br : BitReader) (codeLenLengths : Array Nat) :
    (ForInStep.yield ((br, codeLenLengths) : BitReader × Array Nat)).bindList
        dynamicCodeLenLoopBody (List.range' 5 5) =
      (ForInStep.yield <$> (Prod.swap <$> readDynamicCodeLenLengthsTail5 codeLenLengths br)) := by
  unfold readDynamicCodeLenLengthsTail5 read3Bits?
  simp [dynamicCodeLenLoopBody, List.range', Option.map]
  repeat' (first | split <;> simp_all)

/-- Specializes the first five code-length iterations to the source `MProd` loop state. -/
private lemma bindList_range0_5_eq_head5_mprod (br : BitReader) :
    (ForInStep.yield (⟨br, Array.replicate 19 0⟩ : MProd BitReader (Array Nat))).bindList
        dynamicCodeLenLoopBodyM (List.range' 0 5) =
      (ForInStep.yield <$>
        ((fun r : Array Nat × BitReader => (⟨r.snd, r.fst⟩ : MProd BitReader (Array Nat))) <$>
          readDynamicCodeLenLengthsHead5 br)) := by
  unfold readDynamicCodeLenLengthsHead5 read3Bits?
  simp [dynamicCodeLenLoopBodyM, List.range', Option.map]
  repeat' (first | split <;> simp_all)

/-- Specializes the last five code-length iterations to the source `MProd` loop state. -/
private lemma bindList_range5_5_eq_tail5_mprod (br : BitReader) (codeLenLengths : Array Nat) :
    (ForInStep.yield (⟨br, codeLenLengths⟩ : MProd BitReader (Array Nat))).bindList
        dynamicCodeLenLoopBodyM (List.range' 5 5) =
      (ForInStep.yield <$>
        ((fun r : Array Nat × BitReader => (⟨r.snd, r.fst⟩ : MProd BitReader (Array Nat))) <$>
          readDynamicCodeLenLengthsTail5 codeLenLengths br)) := by
  unfold readDynamicCodeLenLengthsTail5 read3Bits?
  simp [dynamicCodeLenLoopBodyM, List.range', Option.map]
  repeat' (first | split <;> simp_all)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Bridges the concrete ten-step `forIn` loop with the specialized code-length reader helper. -/
lemma readDynamicCodeLenLengths10_eq_forIn_range10 (br : BitReader) :
    forIn (List.range' 0 (6 + 4))
        ((br, Array.replicate 19 0) : BitReader × Array Nat)
        dynamicCodeLenLoopBody =
      Prod.swap <$> readDynamicCodeLenLengths10 br := by
  rw [show List.range' 0 (6 + 4) = List.range' 0 5 ++ List.range' 5 5 by native_decide]
  rw [List.forIn_eq_bindList, ForInStep.bindList_append]
  rw [bindList_range0_5_eq_head5]
  cases hhead : readDynamicCodeLenLengthsHead5 br with
  | none =>
      simp [readDynamicCodeLenLengths10, hhead, Option.map]
  | some head =>
      rcases head with ⟨codeLenLengths, br5⟩
      cases htail : readDynamicCodeLenLengthsTail5 codeLenLengths br5 with
      | none =>
          simp [readDynamicCodeLenLengths10, hhead, htail, bindList_range5_5_eq_tail5,
            Option.map]
      | some tail =>
          simp [readDynamicCodeLenLengths10, hhead, htail, bindList_range5_5_eq_tail5,
            Option.map]

/-- Keeps the same ten-step loop in the source `MProd` state used by unfolded `readDynamicTables`. -/
lemma readDynamicCodeLenLengths10_eq_forIn_range10_mprod (br : BitReader) :
    forIn (List.range' 0 (6 + 4))
        ((⟨br, Array.replicate 19 0⟩ : MProd BitReader (Array Nat)))
        dynamicCodeLenLoopBodyM =
      ((fun r : Array Nat × BitReader => (⟨r.snd, r.fst⟩ : MProd BitReader (Array Nat))) <$>
        readDynamicCodeLenLengths10 br) := by
  rw [show List.range' 0 (6 + 4) = List.range' 0 5 ++ List.range' 5 5 by native_decide]
  rw [List.forIn_eq_bindList, ForInStep.bindList_append]
  rw [bindList_range0_5_eq_head5_mprod]
  cases hhead : readDynamicCodeLenLengthsHead5 br with
  | none =>
      simp [readDynamicCodeLenLengths10, hhead, Option.map]
  | some head =>
      rcases head with ⟨codeLenLengths, br5⟩
      cases htail : readDynamicCodeLenLengthsTail5 codeLenLengths br5 with
      | none =>
          simp [readDynamicCodeLenLengths10, hhead, htail, bindList_range5_5_eq_tail5_mprod,
            Option.map]
      | some tail =>
          simp [readDynamicCodeLenLengths10, hhead, htail, bindList_range5_5_eq_tail5_mprod,
            Option.map]

/-- Reuses extensionality to compare two `readerAt` values built from equal writers and data. -/
lemma readerAt_eq_of_eqs
    {bw1 bw2 : BitWriter} {data1 data2 : ByteArray}
    (hbw : bw1 = bw2) (hdata : data1 = data2)
    (hflush1 : bw1.flush.size ≤ data1.size) (hflush2 : bw2.flush.size ≤ data2.size)
    (hbit1 : bw1.bitPos < 8) (hbit2 : bw2.bitPos < 8) :
    BitWriter.readerAt bw1 data1 hflush1 hbit1 =
      BitWriter.readerAt bw2 data2 hflush2 hbit2 := by
  subst hbw
  subst hdata
  apply BitReader.ext <;> simp [BitWriter.readerAt]

  private lemma readBits_readerAt_writeBits_step
    (bw : BitWriter) (n w restBits restLen : Nat)
    (hn : n < 2 ^ w) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := n ||| (restBits <<< w)
    let lenTot := w + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    br.readBits w
        (by
          have hk : w ≤ lenTot := by omega
          simpa [br, bw', lenTot] using
            (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := w) hk hbit)) =
      (n,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot w) bw'.flush
          (by
            have hk : w ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot w lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot w hbit)) := by
  let bitsTot := n ||| (restBits <<< w)
  let lenTot := w + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  have hread :
      br.readBits w
          (by
            have hk : w ≤ lenTot := by omega
            simpa [br, bw', lenTot] using
              (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := w) hk hbit)) =
        (bitsTot % 2 ^ w,
          BitWriter.readerAt (BitWriter.writeBits bw bitsTot w) bw'.flush
            (by
              have hk : w ≤ lenTot := by omega
              simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot w lenTot hk))
            (bitPos_lt_8_writeBits bw bitsTot w hbit)) := by
    exact
      (readBits_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := w)
        (hk := by omega) hbit hcur)
  have hmod :
      bitsTot % 2 ^ w = n := by
    have h :=
      mod_two_pow_or_shift (a := n) (b := restBits) (k := w) (len := w) (hk := le_rfl)
    simpa [bitsTot, Nat.mod_eq_of_lt hn] using h
  simpa [bitsTot, lenTot, bw', br, hmod] using hread

/-- Extracts the low 5-bit HLIT field from the packed dynamic header prefix. -/
lemma dynamicHeaderPrefixBits_low5 :
    dynamicHeaderPrefixBits % 2 ^ 5 = 31 := by
  native_decide

/-- Extracts the middle 5-bit HDIST field from the packed dynamic header prefix. -/
lemma dynamicHeaderPrefixBits_mid5 :
    (dynamicHeaderPrefixBits >>> 5) % 2 ^ 5 = 31 := by
  native_decide

/-- Extracts the high 4-bit HCLEN field from the packed dynamic header prefix. -/
lemma dynamicHeaderPrefixBits_high4 :
    (dynamicHeaderPrefixBits >>> 10) % 2 ^ 4 = 6 := by
  native_decide

/-- Shifts away the first 14 header bits to expose the code-length table payload. -/
lemma dynamicHeaderReadBits_shift14 (restBits : Nat) :
    dynamicHeaderReadBits restBits >>> 14 = dynamicHeaderCodeLenLensBits restBits := by
  let tail := dynamicHeaderCodeLenLensBits restBits
  have h1 :
      (31 ||| ((31 ||| ((6 ||| (tail <<< 4)) <<< 5)) <<< 5)) >>> 5 =
        31 ||| ((6 ||| (tail <<< 4)) <<< 5) := by
    simpa using
      (shiftRight_or_shiftLeft
        (a := 31) (b := 31 ||| ((6 ||| (tail <<< 4)) <<< 5)) (len := 5) (by decide))
  have h2 :
      (31 ||| ((6 ||| (tail <<< 4)) <<< 5)) >>> 5 =
        6 ||| (tail <<< 4) := by
    simpa using
      (shiftRight_or_shiftLeft
        (a := 31) (b := 6 ||| (tail <<< 4)) (len := 5) (by decide))
  have h3 :
      (6 ||| (tail <<< 4)) >>> 4 = tail := by
    simpa using
      (shiftRight_or_shiftLeft
        (a := 6) (b := tail) (len := 4) (by decide))
  calc
    dynamicHeaderReadBits restBits >>> 14
        = ((dynamicHeaderReadBits restBits >>> 5) >>> 5) >>> 4 := by
            simpa [Nat.add_assoc] using
              (Nat.shiftRight_add (dynamicHeaderReadBits restBits) 10 4).symm
    _ = ((31 ||| ((31 ||| ((6 ||| (tail <<< 4)) <<< 5)) <<< 5)) >>> 5 >>> 5) >>> 4 := by
          simp [dynamicHeaderReadBits, tail]
    _ = ((31 ||| ((6 ||| (tail <<< 4)) <<< 5)) >>> 5) >>> 4 := by rw [h1]
    _ = (6 ||| (tail <<< 4)) >>> 4 := by rw [h2]
    _ = tail := h3
    _ = dynamicHeaderCodeLenLensBits restBits := rfl

/-- Recomputes HLIT directly from the full header bit bundle. -/
lemma dynamicHeaderReadBits_low5 (restBits : Nat) :
    dynamicHeaderReadBits restBits % 2 ^ 5 = 31 := by
  unfold dynamicHeaderReadBits
  simpa using
    (mod_two_pow_or_shift
      (a := 31) (b := 31 ||| ((6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4)) <<< 5))
      (k := 5) (len := 5) (hk := by decide))

/-- Recomputes HDIST directly from the full header bit bundle. -/
lemma dynamicHeaderReadBits_mid5 (restBits : Nat) :
    (dynamicHeaderReadBits restBits >>> 5) % 2 ^ 5 = 31 := by
  have hshift :
      dynamicHeaderReadBits restBits >>> 5 =
        31 ||| ((6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4)) <<< 5) := by
    unfold dynamicHeaderReadBits
    simpa using
      (shiftRight_or_shiftLeft
        (a := 31) (b := 31 ||| ((6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4)) <<< 5))
        (len := 5) (by decide))
  rw [hshift]
  simpa using
    (mod_two_pow_or_shift
      (a := 31) (b := 6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4))
      (k := 5) (len := 5) (hk := by decide))

/-- Recomputes HCLEN directly from the full header bit bundle. -/
lemma dynamicHeaderReadBits_high4 (restBits : Nat) :
    (dynamicHeaderReadBits restBits >>> 10) % 2 ^ 4 = 6 := by
  have hshift5 :
      dynamicHeaderReadBits restBits >>> 5 =
        31 ||| ((6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4)) <<< 5) := by
    unfold dynamicHeaderReadBits
    simpa using
      (shiftRight_or_shiftLeft
        (a := 31) (b := 31 ||| ((6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4)) <<< 5))
        (len := 5) (by decide))
  have hshift10 :
      dynamicHeaderReadBits restBits >>> 10 =
        6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4) := by
    calc
      dynamicHeaderReadBits restBits >>> 10
          = (dynamicHeaderReadBits restBits >>> 5) >>> 5 := by
              simpa using (Nat.shiftRight_add (dynamicHeaderReadBits restBits) 5 5)
      _ = (31 ||| ((6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4)) <<< 5)) >>> 5 := by
            rw [hshift5]
      _ = 6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4) := by
            simpa using
              (shiftRight_or_shiftLeft
                (a := 31) (b := 6 ||| (dynamicHeaderCodeLenLensBits restBits <<< 4))
                (len := 5) (by decide))
  rw [hshift10]
  simpa using
    (mod_two_pow_or_shift
      (a := 6) (b := dynamicHeaderCodeLenLensBits restBits)
      (k := 4) (len := 4) (hk := by decide))

/-- Shifts past the ten 3-bit code-length entries to expose the remaining symbol payload. -/
lemma dynamicHeaderCodeLenLensBits_shift30 (restBits : Nat) :
    dynamicHeaderCodeLenLensBits restBits >>> (3 * dynamicHeaderCodeLenLens.length) =
      dynamicHeaderCodeLenSymsRestBits restBits := by
  have hprefix :
      fixedWidthListBits 3 dynamicHeaderCodeLenLens < 2 ^ (3 * dynamicHeaderCodeLenLens.length) := by
    native_decide
  simpa [dynamicHeaderCodeLenLensBits] using
    (shiftRight_or_shiftLeft
      (a := fixedWidthListBits 3 dynamicHeaderCodeLenLens)
      (b := dynamicHeaderCodeLenSymsRestBits restBits)
      (len := 3 * dynamicHeaderCodeLenLens.length) hprefix)

/-- Shifts past both the 14-bit header and the code-length table payload. -/
lemma dynamicHeaderReadBits_shift44 (restBits : Nat) :
    dynamicHeaderReadBits restBits >>> (14 + 3 * dynamicHeaderCodeLenLens.length) =
      dynamicHeaderCodeLenSymsRestBits restBits := by
  calc
    dynamicHeaderReadBits restBits >>> (14 + 3 * dynamicHeaderCodeLenLens.length)
        = (dynamicHeaderReadBits restBits >>> 14) >>> (3 * dynamicHeaderCodeLenLens.length) := by
            simpa using
              (Nat.shiftRight_add
                (dynamicHeaderReadBits restBits) 14 (3 * dynamicHeaderCodeLenLens.length))
    _ = dynamicHeaderCodeLenSymsRestBits restBits := by
          rw [dynamicHeaderReadBits_shift14, dynamicHeaderCodeLenLensBits_shift30]

/-- Computes the total bit length of the fixed dynamic table header plus an arbitrary suffix. -/
lemma dynamicHeaderReadLen_eq (restLen : Nat) :
    dynamicHeaderReadLen restLen = dynamicHeaderTableLen + restLen := by
  have hlen : dynamicHeaderCodeLenLens.length = 10 := by
    native_decide
  rw [dynamicHeaderTableLen_eq]
  simp [dynamicHeaderReadLen, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen]
  rw [hlen, dynamicHeaderCodeLenSyms_length]
  omega

/-- Removes the initial 14 header bits from the total dynamic header length. -/
lemma dynamicHeaderReadLen_sub14 (restLen : Nat) :
    dynamicHeaderReadLen restLen - 14 = dynamicHeaderCodeLenLensLen restLen := by
  unfold dynamicHeaderReadLen dynamicHeaderCodeLenLensLen dynamicHeaderCodeLenSymsRestLen
  omega

/-- Removes the full 44-bit front section from the total dynamic header length. -/
lemma dynamicHeaderReadLen_sub44 (restLen : Nat) :
    dynamicHeaderReadLen restLen - (14 + 3 * dynamicHeaderCodeLenLens.length) =
      dynamicHeaderCodeLenSymsRestLen restLen := by
  simp [dynamicHeaderReadLen, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen,
    dynamicHeaderCodeLenSyms_length]
  omega

/-- Splits the fixed dynamic table header length into the 44-bit front and the symbol tail. -/
lemma dynamicHeaderTableLen_eq_split :
    dynamicHeaderTableLen =
      (14 + 3 * dynamicHeaderCodeLenLens.length) + 2 * dynamicHeaderCodeLenSyms.length := by
  native_decide

/-- Lower bound ensuring the 5-bit HLIT read is always in range. -/
lemma dynamicHeaderTableLen_ge_5 : 5 ≤ dynamicHeaderTableLen := by
  native_decide

/-- Lower bound ensuring the 5-bit HDIST read is always in range after HLIT. -/
lemma dynamicHeaderTableLen_ge_10 : 10 ≤ dynamicHeaderTableLen := by
  native_decide

/-- Lower bound ensuring the 4-bit HCLEN read is always in range after HLIT and HDIST. -/
lemma dynamicHeaderTableLen_ge_14 : 14 ≤ dynamicHeaderTableLen := by
  native_decide

/-- Promotes the table-length lower bound to the full dynamic header plus suffix. -/
lemma dynamicHeaderReadLen_ge_5 (restLen : Nat) :
    5 ≤ dynamicHeaderReadLen restLen := by
  have hlen : dynamicHeaderReadLen restLen = dynamicHeaderTableLen + restLen := by
    simpa using dynamicHeaderReadLen_eq restLen
  have hbase : 5 ≤ dynamicHeaderTableLen := dynamicHeaderTableLen_ge_5
  omega

/-- Promotes the 10-bit front-header lower bound to the full dynamic header plus suffix. -/
lemma dynamicHeaderReadLen_ge_10 (restLen : Nat) :
    10 ≤ dynamicHeaderReadLen restLen := by
  have hlen : dynamicHeaderReadLen restLen = dynamicHeaderTableLen + restLen := by
    simpa using dynamicHeaderReadLen_eq restLen
  have hbase : 10 ≤ dynamicHeaderTableLen := dynamicHeaderTableLen_ge_10
  omega

/-- Promotes the 14-bit front-header lower bound to the full dynamic header plus suffix. -/
lemma dynamicHeaderReadLen_ge_14 (restLen : Nat) :
    14 ≤ dynamicHeaderReadLen restLen := by
  have hlen : dynamicHeaderReadLen restLen = dynamicHeaderTableLen + restLen := by
    simpa using dynamicHeaderReadLen_eq restLen
  have hbase : 14 ≤ dynamicHeaderTableLen := dynamicHeaderTableLen_ge_14
  omega

/-- Guarantees there are still 5 readable bits after consuming HLIT. -/
lemma dynamicHeaderReadLen_sub5_ge_5 (restLen : Nat) :
    5 ≤ dynamicHeaderReadLen restLen - 5 := by
  have hlen : dynamicHeaderReadLen restLen = dynamicHeaderTableLen + restLen := by
    simpa using dynamicHeaderReadLen_eq restLen
  have hbase : 10 ≤ dynamicHeaderTableLen := dynamicHeaderTableLen_ge_10
  omega

/-- Guarantees there are still 4 readable bits after consuming HLIT and HDIST. -/
lemma dynamicHeaderReadLen_sub10_ge_4 (restLen : Nat) :
    4 ≤ dynamicHeaderReadLen restLen - 10 := by
  have hlen : dynamicHeaderReadLen restLen = dynamicHeaderTableLen + restLen := by
    simpa using dynamicHeaderReadLen_eq restLen
  have hbase : 14 ≤ dynamicHeaderTableLen := dynamicHeaderTableLen_ge_14
  omega

/-- States that the fixed dynamic table header is always contained in the full stream length. -/
lemma dynamicHeaderTableLen_le_readLen (restLen : Nat) :
    dynamicHeaderTableLen ≤ dynamicHeaderReadLen restLen := by
  have hlen : dynamicHeaderReadLen restLen = dynamicHeaderTableLen + restLen := by
    simpa using dynamicHeaderReadLen_eq restLen
  omega

/-- Extracts the literal/length code lengths from the concatenated lengths buffer. -/
lemma dynamicLitLenDistLengths_extract_lit :
    (dynamicLitLenLengths ++ dynamicDistLengths).extract 0 288 = dynamicLitLenLengths := by
  native_decide

/-- Extracts the distance code lengths from the concatenated lengths buffer. -/
lemma dynamicLitLenDistLengths_extract_dist :
    (dynamicLitLenLengths ++ dynamicDistLengths).extract 288 (288 + 32) = dynamicDistLengths := by
  native_decide

/-- Normalizes the literal/length extraction after `extract` expansion in later simp goals. -/
lemma dynamicLitLenDistLengths_extract_lit_expanded :
    dynamicLitLenLengths.extract 0 288 ++
      dynamicDistLengths.extract 0 (288 - dynamicLitLenLengths.size) = dynamicLitLenLengths := by
  native_decide

/-- Normalizes the distance extraction after `extract` expansion in later simp goals. -/
lemma dynamicLitLenDistLengths_extract_dist_expanded :
    dynamicLitLenLengths.extract 288 320 ++
      dynamicDistLengths.extract (288 - dynamicLitLenLengths.size) (320 - dynamicLitLenLengths.size) =
        dynamicDistLengths := by
  native_decide

/-- Re-exports the 3-bit packed code-length table constant inside the read-tables module. -/
lemma fixedWidthListBits_three_dynamicHeaderCodeLenLens :
    fixedWidthListBits 3 dynamicHeaderCodeLenLens = dynamicHeaderCodeLenLenBits := by
  native_decide

private lemma dynamicHeaderCodeLenLensBits_mod_eq
    (restBits k : Nat) (hk : k ≤ 3 * dynamicHeaderCodeLenLens.length) :
    dynamicHeaderCodeLenLensBits restBits % 2 ^ k = dynamicHeaderCodeLenLenBits % 2 ^ k := by
  have h :=
    mod_two_pow_or_shift
      (a := fixedWidthListBits 3 dynamicHeaderCodeLenLens)
      (b := dynamicHeaderCodeLenSymsRestBits restBits)
      (k := k) (len := 3 * dynamicHeaderCodeLenLens.length) hk
  simpa [dynamicHeaderCodeLenLensBits, fixedWidthListBits_three_dynamicHeaderCodeLenLens] using h

private lemma shiftRight_mod_two_pow_one (bits n : Nat) :
    (bits % 2 ^ (n + 1)) >>> 1 = (bits >>> 1) % 2 ^ n := by
  have hdecomp : bits % 2 ^ (n + 1) = (bits % 2) ||| (((bits >>> 1) % 2 ^ n) <<< 1) := by
    simpa using mod_two_pow_decomp bits n
  have hlt : bits % 2 < 2 ^ (1 : Nat) := by
    have : bits % 2 < 2 := Nat.mod_lt _ (by decide)
    simpa using this
  calc
    (bits % 2 ^ (n + 1)) >>> 1
        = ((bits % 2) ||| (((bits >>> 1) % 2 ^ n) <<< 1)) >>> 1 := by rw [hdecomp]
    _ = (bits >>> 1) % 2 ^ n := by
          simpa using
            (shiftRight_or_shiftLeft
              (a := bits % 2) (b := (bits >>> 1) % 2 ^ n) (len := 1) hlt)

private lemma shiftRight_mod_two_pow (bits k n : Nat) :
    (bits % 2 ^ (k + n)) >>> k = (bits >>> k) % 2 ^ n := by
  rw [mod_two_pow_split bits k n]
  have hlt : bits % 2 ^ k < 2 ^ k := by
    exact Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))
  simpa using
    (shiftRight_or_shiftLeft
      (a := bits % 2 ^ k) (b := (bits >>> k) % 2 ^ n) (len := k) hlt)

private lemma dynamicHeaderCodeLenLensBits_shift_mod_three
    (restBits skip : Nat) (hskip : skip + 3 ≤ 3 * dynamicHeaderCodeLenLens.length) :
    (dynamicHeaderCodeLenLensBits restBits >>> skip) % 2 ^ 3 =
      (dynamicHeaderCodeLenLenBits % 2 ^ (skip + 3)) >>> skip := by
  calc
    (dynamicHeaderCodeLenLensBits restBits >>> skip) % 2 ^ 3
        = (dynamicHeaderCodeLenLensBits restBits % 2 ^ (skip + 3)) >>> skip := by
            symm
            simpa [Nat.add_comm] using
              (shiftRight_mod_two_pow (bits := dynamicHeaderCodeLenLensBits restBits) (k := skip) (n := 3))
    _ = (dynamicHeaderCodeLenLenBits % 2 ^ (skip + 3)) >>> skip := by
          rw [dynamicHeaderCodeLenLensBits_mod_eq restBits (skip + 3) hskip]

/-- Reads `k` bits after skipping `skip` bits in a writer-produced stream. -/
lemma readBits_readerAt_writeBits_shift
    (bw : BitWriter) (bits len skip k : Nat)
    (hskip : skip ≤ len) (hk : k ≤ len - skip)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bwFull := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt (BitWriter.writeBits bw bits skip) bwFull.flush
      (by simpa [bwFull] using flush_size_writeBits_prefix bw bits skip len hskip)
      (bitPos_lt_8_writeBits bw bits skip hbit)
    br.readBits k
        (by
          have hsplit :
              bwFull =
                BitWriter.writeBits (BitWriter.writeBits bw bits skip) (bits >>> skip) (len - skip) := by
            calc
              bwFull = BitWriter.writeBits bw bits (skip + (len - skip)) := by
                simp [bwFull, Nat.add_sub_of_le hskip]
              _ = BitWriter.writeBits (BitWriter.writeBits bw bits skip) (bits >>> skip) (len - skip) := by
                simpa using writeBits_split bw bits skip (len - skip)
          have hread :=
            readerAt_writeBits_bound
              (bw := BitWriter.writeBits bw bits skip)
              (bits := bits >>> skip) (len := len - skip) (k := k) hk
              (bitPos_lt_8_writeBits bw bits skip hbit)
          simpa [bwFull, br, hsplit] using hread) =
      ((bits >>> skip) % 2 ^ k,
        BitWriter.readerAt (BitWriter.writeBits bw bits (skip + k)) bwFull.flush
          (by
            have hk' : skip + k ≤ len := by omega
            simpa [bwFull] using flush_size_writeBits_prefix bw bits (skip + k) len hk')
          (bitPos_lt_8_writeBits bw bits (skip + k) hbit)) := by
  let bwFull := BitWriter.writeBits bw bits len
  let bwSkip := BitWriter.writeBits bw bits skip
  let br := BitWriter.readerAt bwSkip bwFull.flush
    (by simpa [bwFull] using flush_size_writeBits_prefix bw bits skip len hskip)
    (bitPos_lt_8_writeBits bw bits skip hbit)
  have hsplit :
      bwFull = BitWriter.writeBits bwSkip (bits >>> skip) (len - skip) := by
    calc
      bwFull = BitWriter.writeBits bw bits (skip + (len - skip)) := by
        simp [bwFull, Nat.add_sub_of_le hskip]
      _ = BitWriter.writeBits bwSkip (bits >>> skip) (len - skip) := by
        simpa [bwSkip] using writeBits_split bw bits skip (len - skip)
  let brNext := BitWriter.readerAt (BitWriter.writeBits bwSkip (bits >>> skip) k) bwFull.flush
    (by
      have hk' : k ≤ len - skip := hk
      simpa [bwFull, hsplit] using
        flush_size_writeBits_prefix bwSkip (bits >>> skip) k (len - skip) hk')
    (bitPos_lt_8_writeBits bwSkip (bits >>> skip) k (bitPos_lt_8_writeBits bw bits skip hbit))
  have hread :
      br.readBits k
          (by
            have hread :=
              readerAt_writeBits_bound
                (bw := bwSkip) (bits := bits >>> skip) (len := len - skip) (k := k) hk
                (bitPos_lt_8_writeBits bw bits skip hbit)
            simpa [br, bwFull, hsplit] using hread) =
        ((bits >>> skip) % 2 ^ k, brNext) := by
    simpa [br, brNext, bwFull, hsplit] using
      (readBits_readerAt_writeBits_prefix
        (bw := bwSkip) (bits := bits >>> skip) (len := len - skip) (k := k) hk
        (bitPos_lt_8_writeBits bw bits skip hbit)
        (curClearAbove_writeBits bw bits skip hbit hcur))
  have hwriter :
      BitWriter.writeBits bwSkip (bits >>> skip) k =
        BitWriter.writeBits bw bits (skip + k) := by
    simpa [bwSkip] using (writeBits_split bw bits skip k).symm
  have hreader :
      brNext =
        BitWriter.readerAt (BitWriter.writeBits bw bits (skip + k)) bwFull.flush
          (by
            have hk' : skip + k ≤ len := by omega
            simpa [bwFull] using flush_size_writeBits_prefix bw bits (skip + k) len hk')
          (bitPos_lt_8_writeBits bw bits (skip + k) hbit) := by
    refine readerAt_eq_of_eqs hwriter rfl _ _ _ _
  simpa [bwFull, br, hreader] using hread

/-- Identifies the reader obtained from a split write with the reader from the combined write. -/
lemma readerAt_writeBits_split_eq
    (bw : BitWriter) (bits len skip k : Nat)
    (hskip : skip ≤ len) (hk : k ≤ len - skip)
    (hbit : bw.bitPos < 8) :
    let bwFull := BitWriter.writeBits bw bits len
    BitWriter.readerAt
      (BitWriter.writeBits (BitWriter.writeBits bw bits skip) (bits >>> skip) k)
      bwFull.flush
      (by
        have hk' : k ≤ len - skip := hk
        have hsplit :
            bwFull =
              BitWriter.writeBits (BitWriter.writeBits bw bits skip) (bits >>> skip) (len - skip) := by
          calc
            bwFull = BitWriter.writeBits bw bits (skip + (len - skip)) := by
              simp [bwFull, Nat.add_sub_of_le hskip]
            _ = BitWriter.writeBits (BitWriter.writeBits bw bits skip) (bits >>> skip) (len - skip) := by
                simpa using writeBits_split bw bits skip (len - skip)
        simpa [bwFull, hsplit] using
          flush_size_writeBits_prefix
            (BitWriter.writeBits bw bits skip) (bits >>> skip) k (len - skip) hk')
      (bitPos_lt_8_writeBits
        (BitWriter.writeBits bw bits skip) (bits >>> skip) k
        (bitPos_lt_8_writeBits bw bits skip hbit)) =
    BitWriter.readerAt (BitWriter.writeBits bw bits (skip + k)) bwFull.flush
      (by
        have hk' : skip + k ≤ len := by omega
        simpa [bwFull] using flush_size_writeBits_prefix bw bits (skip + k) len hk')
      (bitPos_lt_8_writeBits bw bits (skip + k) hbit) := by
  let bwFull := BitWriter.writeBits bw bits len
  let bwSkip := BitWriter.writeBits bw bits skip
  let brNext := BitWriter.readerAt (BitWriter.writeBits bwSkip (bits >>> skip) k) bwFull.flush
    (by
      have hk' : k ≤ len - skip := hk
      have hsplit :
          bwFull = BitWriter.writeBits bwSkip (bits >>> skip) (len - skip) := by
        calc
          bwFull = BitWriter.writeBits bw bits (skip + (len - skip)) := by
            simp [bwFull, Nat.add_sub_of_le hskip]
          _ = BitWriter.writeBits bwSkip (bits >>> skip) (len - skip) := by
              simpa [bwSkip] using writeBits_split bw bits skip (len - skip)
      simpa [bwFull, bwSkip, hsplit] using
        flush_size_writeBits_prefix bwSkip (bits >>> skip) k (len - skip) hk')
    (bitPos_lt_8_writeBits bwSkip (bits >>> skip) k (bitPos_lt_8_writeBits bw bits skip hbit))
  have hwriter :
      BitWriter.writeBits bwSkip (bits >>> skip) k =
        BitWriter.writeBits bw bits (skip + k) := by
    simpa [bwSkip] using (writeBits_split bw bits skip k).symm
  have hreader :
      brNext =
        BitWriter.readerAt (BitWriter.writeBits bw bits (skip + k)) bwFull.flush
          (by
            have hk' : skip + k ≤ len := by omega
            simpa [bwFull] using flush_size_writeBits_prefix bw bits (skip + k) len hk')
          (bitPos_lt_8_writeBits bw bits (skip + k) hbit) := by
    refine readerAt_eq_of_eqs hwriter rfl _ _ _ _
  simpa [bwFull, bwSkip, brNext] using hreader

private lemma read3Bits?_readerAt_writeBits_shift
    (bw : BitWriter) (bits len skip : Nat)
    (hskip : skip ≤ len) (hk : 3 ≤ len - skip)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bwFull := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt (BitWriter.writeBits bw bits skip) bwFull.flush
      (by simpa [bwFull] using flush_size_writeBits_prefix bw bits skip len hskip)
      (bitPos_lt_8_writeBits bw bits skip hbit)
    read3Bits? br =
      some
        (((bits >>> skip) % 2 ^ 3),
          BitWriter.readerAt (BitWriter.writeBits bw bits (skip + 3)) bwFull.flush
            (by
              have hk' : skip + 3 ≤ len := by omega
              simpa [bwFull] using flush_size_writeBits_prefix bw bits (skip + 3) len hk')
            (bitPos_lt_8_writeBits bw bits (skip + 3) hbit)) := by
  let bwFull := BitWriter.writeBits bw bits len
  let bwSkip := BitWriter.writeBits bw bits skip
  let br := BitWriter.readerAt bwSkip bwFull.flush
    (by simpa [bwFull] using flush_size_writeBits_prefix bw bits skip len hskip)
    (bitPos_lt_8_writeBits bw bits skip hbit)
  have hsplit :
      bwFull = BitWriter.writeBits bwSkip (bits >>> skip) (len - skip) := by
    calc
      bwFull = BitWriter.writeBits bw bits (skip + (len - skip)) := by
        simp [bwFull, Nat.add_sub_of_le hskip]
      _ = BitWriter.writeBits bwSkip (bits >>> skip) (len - skip) := by
        simpa [bwSkip] using writeBits_split bw bits skip (len - skip)
  let brNext := BitWriter.readerAt (BitWriter.writeBits bwSkip (bits >>> skip) 3) bwFull.flush
    (by
      simpa [bwFull, hsplit] using
        flush_size_writeBits_prefix bwSkip (bits >>> skip) 3 (len - skip) hk)
    (bitPos_lt_8_writeBits bwSkip (bits >>> skip) 3
      (bitPos_lt_8_writeBits bw bits skip hbit))
  have hbound : br.bitIndex + 3 ≤ br.data.size * 8 := by
    have hread :=
      readerAt_writeBits_bound
        (bw := bwSkip) (bits := bits >>> skip) (len := len - skip) (k := 3) hk
        (bitPos_lt_8_writeBits bw bits skip hbit)
    simpa [br, bwFull, hsplit] using hread
  have hread :=
    readBits_readerAt_writeBits_shift
      (bw := bw) (bits := bits) (len := len) (skip := skip) (k := 3)
      hskip hk hbit hcur
  unfold read3Bits?
  change
    (if h : br.bitIndex + 3 ≤ br.data.size * 8 then some (br.readBits 3 h) else none) =
      some
        (((bits >>> skip) % 2 ^ 3),
          BitWriter.readerAt (BitWriter.writeBits bw bits (skip + 3)) bwFull.flush
            (by
              have hk' : skip + 3 ≤ len := by omega
              simpa [bwFull] using flush_size_writeBits_prefix bw bits (skip + 3) len hk')
            (bitPos_lt_8_writeBits bw bits (skip + 3) hbit))
  simpa [hbound] using congrArg some hread

private lemma read3Bits_dynamicHeaderCodeLenLens_readerAt_writeBits
    (bw : BitWriter) (restBits restLen skip expected : Nat)
    (hprefix : skip + 3 ≤ 3 * dynamicHeaderCodeLenLens.length)
    (hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (skip + 3)) >>> skip) = expected)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderCodeLenLensBits restBits
    let lenTot := dynamicHeaderCodeLenLensLen restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt (BitWriter.writeBits bw bitsTot skip) bw'.flush
      (by
        have hk : skip ≤ lenTot := by
          have hlen : 3 * dynamicHeaderCodeLenLens.length ≤ lenTot := by
            simp [lenTot, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen]
          omega
        simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot skip lenTot hk)
      (bitPos_lt_8_writeBits bw bitsTot skip hbit)
    read3Bits? br =
      some
        (expected,
          BitWriter.readerAt (BitWriter.writeBits bw bitsTot (skip + 3)) bw'.flush
            (by
              have hk : skip + 3 ≤ lenTot := by
                have hlen : 3 * dynamicHeaderCodeLenLens.length ≤ lenTot := by
                  simp [lenTot, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen]
                omega
              simpa [bw', lenTot] using
                flush_size_writeBits_prefix bw bitsTot (skip + 3) lenTot hk)
            (bitPos_lt_8_writeBits bw bitsTot (skip + 3) hbit)) := by
  let bitsTot := dynamicHeaderCodeLenLensBits restBits
  let lenTot := dynamicHeaderCodeLenLensLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt (BitWriter.writeBits bw bitsTot skip) bw'.flush
    (by
      have hk : skip ≤ lenTot := by
        have hlen : 3 * dynamicHeaderCodeLenLens.length ≤ lenTot := by
          simp [lenTot, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen]
        omega
      simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot skip lenTot hk)
    (bitPos_lt_8_writeBits bw bitsTot skip hbit)
  have hstep :=
    read3Bits?_readerAt_writeBits_shift
      (bw := bw) (bits := bitsTot) (len := lenTot) (skip := skip)
      (by
        have hlen : 3 * dynamicHeaderCodeLenLens.length ≤ lenTot := by
          simp [lenTot, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen]
        omega)
      (by
        have hlen : 3 * dynamicHeaderCodeLenLens.length ≤ lenTot := by
          simp [lenTot, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen]
        omega)
      hbit hcur
  have hmod :
      (bitsTot >>> skip) % 2 ^ 3 =
        ((dynamicHeaderCodeLenLenBits % 2 ^ (skip + 3)) >>> skip) := by
    simpa [bitsTot] using dynamicHeaderCodeLenLensBits_shift_mod_three restBits skip hprefix
  have hstep' :
      read3Bits? br =
        some ((bitsTot >>> skip) % 2 ^ 3,
          BitWriter.readerAt (BitWriter.writeBits bw bitsTot (skip + 3)) bw'.flush
            (by
              have hk : skip + 3 ≤ lenTot := by
                have hlen : 3 * dynamicHeaderCodeLenLens.length ≤ lenTot := by
                  simp [lenTot, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen]
                omega
              simpa [bw', lenTot] using
                flush_size_writeBits_prefix bw bitsTot (skip + 3) lenTot hk)
            (bitPos_lt_8_writeBits bw bitsTot (skip + 3) hbit)) := by
    simpa [br, bw', lenTot] using hstep
  rw [hmod, hexpected] at hstep'
  exact hstep'

/-- Records that the fixed code-length table front section contains ten entries. -/
lemma dynamicHeaderCodeLenLens_length :
    dynamicHeaderCodeLenLens.length = 10 := by
  native_decide

private def dynamicCodeLenLensReaderAt
    (bw : BitWriter) (restBits restLen skip : Nat)
    (hskip : skip ≤ dynamicHeaderCodeLenLensLen restLen)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bitsTot := dynamicHeaderCodeLenLensBits restBits
  let lenTot := dynamicHeaderCodeLenLensLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  BitWriter.readerAt (BitWriter.writeBits bw bitsTot skip) bw'.flush
    (by simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot skip lenTot hskip)
    (bitPos_lt_8_writeBits bw bitsTot skip hbit)

def dynamicCodeLenLengthsHead5 : Array Nat := Id.run do
  let mut arr : Array Nat := Array.replicate 19 0
  arr := arr.set! 16 0
  arr := arr.set! 17 0
  arr := arr.set! 18 0
  arr := arr.set! 0 0
  arr := arr.set! 8 2
  return arr

private lemma dynamicCodeLenLengthsTail5Filled_eq :
    (let codeLenLengths := dynamicCodeLenLengthsHead5.set! 7 2
     let codeLenLengths := codeLenLengths.set! 9 2
     let codeLenLengths := codeLenLengths.set! 6 0
     let codeLenLengths := codeLenLengths.set! 10 0
     codeLenLengths.set! 5 2) = dynamicCodeLenLengthsFilled := by
  native_decide

def dynamicCodeLenLensAfterReader
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8) : BitReader :=
  dynamicCodeLenLensReaderAt bw restBits restLen (3 * dynamicHeaderCodeLenLens.length)
    (by
      have hlenTot : dynamicHeaderCodeLenLensLen restLen = 670 + restLen := by
        simp [dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen,
          dynamicHeaderCodeLenSyms_length, dynamicHeaderCodeLenLens_length]
        omega
      rw [hlenTot, dynamicHeaderCodeLenLens_length]
      omega)
    hbit

/-- Normalizes the code-length-table payload length to its concrete `670 + restLen` form. -/
lemma dynamicHeaderCodeLenLensLen_eq_670 (restLen : Nat) :
    dynamicHeaderCodeLenLensLen restLen = 670 + restLen := by
  simp [dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen,
    dynamicHeaderCodeLenSyms_length, dynamicHeaderCodeLenLens_length]
  omega

/-- Shows the code-length table payload is long enough to contain its ten 3-bit entries. -/
lemma dynamicHeaderCodeLenLensLen_ge_codeLenBits (restLen : Nat) :
    3 * dynamicHeaderCodeLenLens.length ≤ dynamicHeaderCodeLenLensLen restLen := by
  simp [dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen]

/-- Shows the trailing code-length-symbol payload is long enough for all ten 2-bit symbols. -/
lemma dynamicHeaderCodeLenSymsRestLen_ge_codeLenSyms (restLen : Nat) :
    2 * dynamicHeaderCodeLenSyms.length ≤ dynamicHeaderCodeLenSymsRestLen restLen := by
  simp [dynamicHeaderCodeLenSymsRestLen]

private lemma dynamicCodeLenLensReaderAt_step
    (bw : BitWriter) (restBits restLen skip expected : Nat)
    (hprefix : skip + 3 ≤ 3 * dynamicHeaderCodeLenLens.length)
    (hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (skip + 3)) >>> skip) = expected)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    read3Bits?
        (dynamicCodeLenLensReaderAt bw restBits restLen skip
          (by
            have hlen : 3 * dynamicHeaderCodeLenLens.length ≤ dynamicHeaderCodeLenLensLen restLen := by
              exact dynamicHeaderCodeLenLensLen_ge_codeLenBits restLen
            omega)
          hbit) =
      some
        (expected,
          dynamicCodeLenLensReaderAt bw restBits restLen (skip + 3)
            (by
              have hlen : 3 * dynamicHeaderCodeLenLens.length ≤ dynamicHeaderCodeLenLensLen restLen := by
                exact dynamicHeaderCodeLenLensLen_ge_codeLenBits restLen
              omega)
            hbit) := by
  let bitsTot := dynamicHeaderCodeLenLensBits restBits
  let lenTot := dynamicHeaderCodeLenLensLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  have hlenTot : lenTot = 670 + restLen := by
    simpa [lenTot] using dynamicHeaderCodeLenLensLen_eq_670 restLen
  simpa [dynamicCodeLenLensReaderAt, bitsTot, lenTot, bw', hlenTot] using
    read3Bits_dynamicHeaderCodeLenLens_readerAt_writeBits
      (bw := bw) (restBits := restBits) (restLen := restLen) (skip := skip)
      (expected := expected) hprefix hexpected hbit hcur

def dynamicCodeLenSymsReaderAt
    (bw : BitWriter) (restBits restLen skip : Nat)
    (hskip : skip ≤ dynamicHeaderCodeLenSymsRestLen restLen)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bitsTot := dynamicHeaderCodeLenSymsRestBits restBits
  let lenTot := dynamicHeaderCodeLenSymsRestLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  BitWriter.readerAt (BitWriter.writeBits bw bitsTot skip) bw'.flush
    (by simpa [bw', lenTot] using flush_size_writeBits_prefix bw bitsTot skip lenTot hskip)
    (bitPos_lt_8_writeBits bw bitsTot skip hbit)

def dynamicTablesAfterHeaderReaderAt
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bitsTot := dynamicHeaderCodeLenLensBits restBits
  let bw30 := BitWriter.writeBits bw bitsTot (3 * dynamicHeaderCodeLenLens.length)
  dynamicCodeLenSymsReaderAt bw30 restBits restLen (2 * dynamicHeaderCodeLenSyms.length)
    (by simpa using dynamicHeaderCodeLenSymsRestLen_ge_codeLenSyms restLen)
    (bitPos_lt_8_writeBits bw bitsTot (3 * dynamicHeaderCodeLenLens.length) hbit)

def dynamicTablesReaderAt
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bitsTot := dynamicHeaderReadBits restBits
  let lenTot := dynamicHeaderReadLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  BitWriter.readerAt
    (BitWriter.writeBits bw bitsTot dynamicHeaderTableLen)
    bw'.flush
    (by
      have hk : dynamicHeaderTableLen ≤ lenTot := by
        simpa [lenTot] using dynamicHeaderTableLen_le_readLen restLen
      simpa [bw', lenTot] using
        (flush_size_writeBits_prefix bw bitsTot dynamicHeaderTableLen lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot dynamicHeaderTableLen hbit)

private lemma readDynamicCodeLenLengthsTail5_of_reads
    (bw : BitWriter) (restBits restLen : Nat) (hbit : bw.bitPos < 8)
    (br5 br6 br7 br8 br9 br10 : BitReader)
    (hread5 : read3Bits? br5 = some (2, br6))
    (hread6 : read3Bits? br6 = some (2, br7))
    (hread7 : read3Bits? br7 = some (0, br8))
    (hread8 : read3Bits? br8 = some (0, br9))
    (hread9 : read3Bits? br9 = some (2, br10))
    (hbr10 : br10 = dynamicCodeLenLensAfterReader bw restBits restLen hbit) :
    readDynamicCodeLenLengthsTail5 dynamicCodeLenLengthsHead5 br5 =
      some (dynamicCodeLenLengthsFilled, dynamicCodeLenLensAfterReader bw restBits restLen hbit) := by
  unfold readDynamicCodeLenLengthsTail5
  rw [hread5]
  simp
  rw [hread6]
  simp
  rw [hread7]
  simp
  rw [hread8]
  simp
  rw [hread9]
  simpa [hbr10] using
    congrArg (fun arr => some (arr, br10)) dynamicCodeLenLengthsTail5Filled_eq

def readDynamicTablesAfterHeader (br : BitReader) :
    Option (Huffman × Huffman × BitReader) := do
  let (codeLenLengths, brCur) ← readDynamicCodeLenLengths10 br
  let codeLenTable ← mkHuffman codeLenLengths
  let total := (31 + 257) + (31 + 1)
  let lengths0 : Array Nat := Array.mkEmpty total
  let (lengths, brNext) ←
    readDynamicTablesLengthsFuel (brCur.data.size * 8 + 1) total codeLenTable brCur lengths0
  let brCur := brNext
  if lengths.size != total then
    none
  let litLenLengths := lengths.extract 0 (31 + 257)
  let distLengths := lengths.extract (31 + 257) ((31 + 257) + (31 + 1))
  let litLenTable ← mkHuffman litLenLengths
  let distTable ← mkHuffman distLengths
  return (litLenTable, distTable, brCur)

private def finishDynamicTablesAfterCodeLenLengths (br : BitReader) :
    Option (Huffman × Huffman × BitReader) := do
  let total := (31 + 257) + (31 + 1)
  let lengths0 : Array Nat := Array.mkEmpty total
  let (lengths, brNext) ←
    readDynamicTablesLengthsFuel (br.data.size * 8 + 1) total dynamicCodeLenHuffman br lengths0
  let brCur := brNext
  if lengths.size != total then
    none
  let litLenLengths := lengths.extract 0 (31 + 257)
  let distLengths := lengths.extract (31 + 257) ((31 + 257) + (31 + 1))
  let litLenTable ← mkHuffman litLenLengths
  let distTable ← mkHuffman distLengths
  return (litLenTable, distTable, brCur)

private lemma readDynamicTablesAfterHeader_eq_finish
    {br brNext : BitReader}
    (hread : readDynamicCodeLenLengths10 br = some (dynamicCodeLenLengthsFilled, brNext))
    (hmk : mkHuffman dynamicCodeLenLengthsFilled = some dynamicCodeLenHuffman) :
    readDynamicTablesAfterHeader br = finishDynamicTablesAfterCodeLenLengths brNext := by
  unfold readDynamicTablesAfterHeader finishDynamicTablesAfterCodeLenLengths
  simp [hread, hmk]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Replays the first five 3-bit code-length reads on the concrete dynamic header stream. -/
lemma readDynamicCodeLenLengthsHead5_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderCodeLenLensBits restBits
    let lenTot := dynamicHeaderCodeLenLensLen restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    readDynamicCodeLenLengthsHead5 br =
      some
        (dynamicCodeLenLengthsHead5,
          dynamicCodeLenLensReaderAt bw restBits restLen 15 (by
            have hlenTot : lenTot = 670 + restLen := by
              simp [lenTot, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen,
                dynamicHeaderCodeLenSyms_length, dynamicHeaderCodeLenLens_length]
              omega
            omega) hbit) := by
  let bitsTot := dynamicHeaderCodeLenLensBits restBits
  let lenTot := dynamicHeaderCodeLenLensLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  have hlenTot : lenTot = 670 + restLen := by
    simpa [lenTot] using dynamicHeaderCodeLenLensLen_eq_670 restLen
  let br1 := dynamicCodeLenLensReaderAt bw restBits restLen 3 (by omega) hbit
  let br2 := dynamicCodeLenLensReaderAt bw restBits restLen 6 (by omega) hbit
  let br3 := dynamicCodeLenLensReaderAt bw restBits restLen 9 (by omega) hbit
  let br4 := dynamicCodeLenLensReaderAt bw restBits restLen 12 (by omega) hbit
  let br5 := dynamicCodeLenLensReaderAt bw restBits restLen 15 (by omega) hbit
  have hread0 : read3Bits? br = some (0, br1) := by
    have hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (0 + 3)) >>> 0) = 0 := by
      native_decide
    simpa [bitsTot, br, bw', lenTot] using
      dynamicCodeLenLensReaderAt_step
        (bw := bw) (restBits := restBits) (restLen := restLen) (skip := 0) (expected := 0)
        (by simp [dynamicHeaderCodeLenLens_length]) hexpected hbit hcur
  have hread1 : read3Bits? br1 = some (0, br2) := by
    have hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (3 + 3)) >>> 3) = 0 := by
      native_decide
    simpa [bitsTot, br1, bw', br2, lenTot, hlenTot] using
      dynamicCodeLenLensReaderAt_step
        (bw := bw) (restBits := restBits) (restLen := restLen) (skip := 3) (expected := 0)
        (by simp [dynamicHeaderCodeLenLens_length]) hexpected hbit hcur
  have hread2 : read3Bits? br2 = some (0, br3) := by
    have hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (6 + 3)) >>> 6) = 0 := by
      native_decide
    simpa [bitsTot, br2, bw', br3, lenTot, hlenTot] using
      dynamicCodeLenLensReaderAt_step
        (bw := bw) (restBits := restBits) (restLen := restLen) (skip := 6) (expected := 0)
        (by simp [dynamicHeaderCodeLenLens_length]) hexpected hbit hcur
  have hread3 : read3Bits? br3 = some (0, br4) := by
    have hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (9 + 3)) >>> 9) = 0 := by
      native_decide
    simpa [bitsTot, br3, bw', br4, lenTot, hlenTot] using
      dynamicCodeLenLensReaderAt_step
        (bw := bw) (restBits := restBits) (restLen := restLen) (skip := 9) (expected := 0)
        (by simp [dynamicHeaderCodeLenLens_length]) hexpected hbit hcur
  have hread4 : read3Bits? br4 = some (2, br5) := by
    have hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (12 + 3)) >>> 12) = 2 := by
      native_decide
    have hstep4 :
        read3Bits? (dynamicCodeLenLensReaderAt bw restBits restLen 12 (by omega) hbit) =
          some (2, dynamicCodeLenLensReaderAt bw restBits restLen 15 (by omega) hbit) :=
      @dynamicCodeLenLensReaderAt_step bw restBits restLen 12 2
        (by simp [dynamicHeaderCodeLenLens_length]) hexpected hbit hcur
    simpa [bitsTot, br4, bw', br5, lenTot, hlenTot] using hstep4
  unfold readDynamicCodeLenLengthsHead5
  simp [bitsTot, lenTot, bw', br, br5, hread0, hread1, hread2, hread3, hread4,
    dynamicCodeLenLengthsHead5]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Replays the last five 3-bit code-length reads on the concrete dynamic header stream. -/
lemma readDynamicCodeLenLengthsTail5_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderCodeLenLensBits restBits
    let lenTot := dynamicHeaderCodeLenLensLen restLen
    let _bw := BitWriter.writeBits bw bitsTot lenTot
    let br5 := dynamicCodeLenLensReaderAt bw restBits restLen 15 (by
      have hlenTot : lenTot = 670 + restLen := by
        simp [lenTot, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen,
          dynamicHeaderCodeLenSyms_length, dynamicHeaderCodeLenLens_length]
        omega
      omega) hbit
    readDynamicCodeLenLengthsTail5 dynamicCodeLenLengthsHead5 br5 =
      some (dynamicCodeLenLengthsFilled, dynamicCodeLenLensAfterReader bw restBits restLen hbit) := by
  let bitsTot := dynamicHeaderCodeLenLensBits restBits
  let lenTot := dynamicHeaderCodeLenLensLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  have hlenTot : lenTot = 670 + restLen := by
    simpa [lenTot] using dynamicHeaderCodeLenLensLen_eq_670 restLen
  let br5 := dynamicCodeLenLensReaderAt bw restBits restLen 15 (by omega) hbit
  let br6 := dynamicCodeLenLensReaderAt bw restBits restLen 18 (by omega) hbit
  let br7 := dynamicCodeLenLensReaderAt bw restBits restLen 21 (by omega) hbit
  let br8 := dynamicCodeLenLensReaderAt bw restBits restLen 24 (by omega) hbit
  let br9 := dynamicCodeLenLensReaderAt bw restBits restLen 27 (by omega) hbit
  let br10 := dynamicCodeLenLensReaderAt bw restBits restLen 30 (by omega) hbit
  have hread5 : read3Bits? br5 = some (2, br6) := by
    have hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (15 + 3)) >>> 15) = 2 := by
      native_decide
    simpa [bitsTot, br5, bw', br6, lenTot, hlenTot] using
      dynamicCodeLenLensReaderAt_step
        (bw := bw) (restBits := restBits) (restLen := restLen) (skip := 15) (expected := 2)
        (by simp [dynamicHeaderCodeLenLens_length]) hexpected hbit hcur
  have hread6 : read3Bits? br6 = some (2, br7) := by
    have hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (18 + 3)) >>> 18) = 2 := by
      native_decide
    simpa [bitsTot, br6, bw', br7, lenTot, hlenTot] using
      dynamicCodeLenLensReaderAt_step
        (bw := bw) (restBits := restBits) (restLen := restLen) (skip := 18) (expected := 2)
        (by simp [dynamicHeaderCodeLenLens_length]) hexpected hbit hcur
  have hread7 : read3Bits? br7 = some (0, br8) := by
    have hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (21 + 3)) >>> 21) = 0 := by
      native_decide
    simpa [bitsTot, br7, bw', br8, lenTot, hlenTot] using
      dynamicCodeLenLensReaderAt_step
        (bw := bw) (restBits := restBits) (restLen := restLen) (skip := 21) (expected := 0)
        (by simp [dynamicHeaderCodeLenLens_length]) hexpected hbit hcur
  have hread8 : read3Bits? br8 = some (0, br9) := by
    have hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (24 + 3)) >>> 24) = 0 := by
      native_decide
    simpa [bitsTot, br8, bw', br9, lenTot, hlenTot] using
      dynamicCodeLenLensReaderAt_step
        (bw := bw) (restBits := restBits) (restLen := restLen) (skip := 24) (expected := 0)
        (by simp [dynamicHeaderCodeLenLens_length]) hexpected hbit hcur
  have hread9 : read3Bits? br9 = some (2, br10) := by
    have hexpected : ((dynamicHeaderCodeLenLenBits % 2 ^ (27 + 3)) >>> 27) = 2 := by
      native_decide
    simpa [bitsTot, br9, bw', br10, lenTot, hlenTot] using
      dynamicCodeLenLensReaderAt_step
        (bw := bw) (restBits := restBits) (restLen := restLen) (skip := 27) (expected := 2)
        (by simp [dynamicHeaderCodeLenLens_length]) hexpected hbit hcur
  have hbr10 : br10 = dynamicCodeLenLensAfterReader bw restBits restLen hbit := by
    simp [br10, dynamicCodeLenLensAfterReader, dynamicCodeLenLensReaderAt,
      dynamicHeaderCodeLenLens_length]
  have hgoal :=
    readDynamicCodeLenLengthsTail5_of_reads
      (bw := bw) (restBits := restBits) (restLen := restLen) (hbit := hbit)
      (br5 := br5) (br6 := br6) (br7 := br7) (br8 := br8) (br9 := br9) (br10 := br10)
      hread5 hread6 hread7 hread8 hread9 hbr10
  simpa [bitsTot, lenTot, bw', br5] using hgoal

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Combines the head and tail proofs into the full ten-entry code-length-table read. -/
lemma readDynamicCodeLenLengths10_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderCodeLenLensBits restBits
    let lenTot := dynamicHeaderCodeLenLensLen restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    readDynamicCodeLenLengths10 br =
      some (dynamicCodeLenLengthsFilled, dynamicCodeLenLensAfterReader bw restBits restLen hbit) := by
  let bitsTot := dynamicHeaderCodeLenLensBits restBits
  let lenTot := dynamicHeaderCodeLenLensLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br5 := dynamicCodeLenLensReaderAt bw restBits restLen 15 (by
    have hlenTot : lenTot = 670 + restLen := by
      simp [lenTot, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen,
        dynamicHeaderCodeLenSyms_length, dynamicHeaderCodeLenLens_length]
      omega
    omega) hbit
  have hhead :=
    readDynamicCodeLenLengthsHead5_readerAt_writeBits
      (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur
  have htail :=
    readDynamicCodeLenLengthsTail5_readerAt_writeBits
      (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur
  unfold readDynamicCodeLenLengths10
  have hhead' : readDynamicCodeLenLengthsHead5 br = some (dynamicCodeLenLengthsHead5, br5) := by
    simpa [br, bw', br5] using hhead
  have htail' :
      readDynamicCodeLenLengthsTail5 dynamicCodeLenLengthsHead5 br5 =
        some (dynamicCodeLenLengthsFilled, dynamicCodeLenLensAfterReader bw restBits restLen hbit) := by
    simpa [br5, bw'] using htail
  have hgoal : readDynamicCodeLenLengths10 br =
      some (dynamicCodeLenLengthsFilled, dynamicCodeLenLensAfterReader bw restBits restLen hbit) := by
    unfold readDynamicCodeLenLengths10
    rw [hhead']
    simpa using htail'
  simpa [bitsTot, lenTot, bw', br] using hgoal

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
private lemma finishDynamicTablesAfterCodeLenLengths_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderCodeLenSymsRestBits restBits
    let lenTot := dynamicHeaderCodeLenSymsRestLen restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    finishDynamicTablesAfterCodeLenLengths br =
      some
        (fixedLitLenHuffman, fixedDistHuffman,
          dynamicCodeLenSymsReaderAt bw restBits restLen (2 * dynamicHeaderCodeLenSyms.length)
            (by simpa using dynamicHeaderCodeLenSymsRestLen_ge_codeLenSyms restLen)
            hbit) := by
  let bitsTot := dynamicHeaderCodeLenSymsRestBits restBits
  let lenTot := dynamicHeaderCodeLenSymsRestLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  have hfuel :
      dynamicHeaderCodeLenSyms.length + 1 ≤ br.data.size * 8 + 1 := by
    have hflush :
        bw'.flush.size * 8 ≥ bw'.bitCount := by
      exact flush_size_mul_ge_bitCount (bw := bw')
        (hbit := bitPos_lt_8_writeBits bw bitsTot lenTot hbit)
    have hcount :
        dynamicHeaderCodeLenSyms.length ≤ bw'.bitCount := by
      rw [bitCount_writeBits]
      simp [lenTot, dynamicHeaderCodeLenSymsRestLen]
      omega
    have hdata : br.data.size = bw'.flush.size := by
      rfl
    have hsize : dynamicHeaderCodeLenSyms.length ≤ br.data.size * 8 := by
      calc
        dynamicHeaderCodeLenSyms.length ≤ bw'.bitCount := hcount
        _ ≤ bw'.flush.size * 8 := by omega
        _ = br.data.size * 8 := by simp [hdata]
    exact Nat.succ_le_succ hsize
  have hreadLengths :=
    readDynamicTablesLengthsFuel_dynamicHeaderCodeLenSyms_readerAt_writeBits
      (bw := bw) (fuel := br.data.size * 8 + 1)
      (restBits := restBits) (restLen := restLen) hfuel hbit hcur
  have htotal :
      (dynamicLitLenLengths ++ dynamicDistLengths).size = (31 + 257) + (31 + 1) := by
    simp [dynamicLitLenLengths_size, dynamicDistLengths_size]
  have hreadLengths' :
      readDynamicTablesLengthsFuel
          (br.data.size * 8 + 1) ((31 + 257) + (31 + 1)) dynamicCodeLenHuffman br
          #[] =
        some
          (dynamicLitLenLengths ++ dynamicDistLengths,
            dynamicCodeLenSymsReaderAt bw restBits restLen (2 * dynamicHeaderCodeLenSyms.length)
              (by simpa using dynamicHeaderCodeLenSymsRestLen_ge_codeLenSyms restLen)
              hbit) := by
    simpa [br, bw', bitsTot, lenTot, htotal] using hreadLengths
  have hsize320 : (dynamicLitLenLengths ++ dynamicDistLengths).size = 320 := by
    simpa using htotal
  unfold finishDynamicTablesAfterCodeLenLengths
  dsimp
  rw [hreadLengths']
  simp [Option.bind, hsize320, dynamicCodeLenSymsReaderAt]
  rw [dynamicLitLenDistLengths_extract_lit_expanded,
    dynamicLitLenDistLengths_extract_dist_expanded]
  rw [mkHuffman_dynamicLitLenLengths, mkHuffman_dynamicDistLengths]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 5000000 in
/-- Finishes the post-header dynamic-table read on the exact stream emitted by the encoder. -/
lemma readDynamicTablesAfterHeader_readerAt_writeBits
    (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := dynamicHeaderCodeLenLensBits restBits
    let lenTot := dynamicHeaderCodeLenLensLen restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    readDynamicTablesAfterHeader br =
      some
        (fixedLitLenHuffman, fixedDistHuffman,
          dynamicTablesAfterHeaderReaderAt bw restBits restLen hbit) := by
  let bitsTot := dynamicHeaderCodeLenLensBits restBits
  let lenTot := dynamicHeaderCodeLenLensLen restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let bw30 := BitWriter.writeBits bw bitsTot (3 * dynamicHeaderCodeLenLens.length)
  have hbit30 : bw30.bitPos < 8 := by
    exact bitPos_lt_8_writeBits bw bitsTot (3 * dynamicHeaderCodeLenLens.length) hbit
  have hcur30 : bw30.curClearAbove := by
    exact curClearAbove_writeBits bw bitsTot (3 * dynamicHeaderCodeLenLens.length) hbit hcur
  have hreadLens :=
    readDynamicCodeLenLengths10_readerAt_writeBits
      (bw := bw) (restBits := restBits) (restLen := restLen) hbit hcur
  have hmkCodeLen :
      mkHuffman dynamicCodeLenLengthsFilled = some dynamicCodeLenHuffman := by
    simpa [dynamicCodeLenLengthsFilled_eq] using mkHuffman_dynamicCodeLenLengths
  have hbw30Full :
      bw' = BitWriter.writeBits bw30 (dynamicHeaderCodeLenSymsRestBits restBits)
        (dynamicHeaderCodeLenSymsRestLen restLen) := by
    calc
      bw' = BitWriter.writeBits bw bitsTot
          ((3 * dynamicHeaderCodeLenLens.length) + (lenTot - (3 * dynamicHeaderCodeLenLens.length))) := by
            have hk : 3 * dynamicHeaderCodeLenLens.length ≤ lenTot := by
              simp [lenTot, dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen]
            simp [bw', Nat.add_sub_of_le hk]
      _ = BitWriter.writeBits
            (BitWriter.writeBits bw bitsTot (3 * dynamicHeaderCodeLenLens.length))
            (bitsTot >>> (3 * dynamicHeaderCodeLenLens.length))
            (lenTot - (3 * dynamicHeaderCodeLenLens.length)) := by
              simpa using
                writeBits_split bw bitsTot (3 * dynamicHeaderCodeLenLens.length)
                  (lenTot - (3 * dynamicHeaderCodeLenLens.length))
      _ = BitWriter.writeBits bw30 (dynamicHeaderCodeLenSymsRestBits restBits)
            (dynamicHeaderCodeLenSymsRestLen restLen) := by
              simp [bitsTot, bw30, dynamicHeaderCodeLenLensBits_shift30, lenTot,
                dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen]
  have hfull30Flush :
      (BitWriter.writeBits bw30 (dynamicHeaderCodeLenSymsRestBits restBits)
        (dynamicHeaderCodeLenSymsRestLen restLen)).flush = bw'.flush := by
    simpa [bw'] using congrArg BitWriter.flush hbw30Full.symm
  have hbr30Start :
      dynamicCodeLenLensAfterReader bw restBits restLen hbit =
        BitWriter.readerAt bw30
          (BitWriter.writeBits bw30 (dynamicHeaderCodeLenSymsRestBits restBits)
            (dynamicHeaderCodeLenSymsRestLen restLen)).flush
          (flush_size_writeBits_le bw30 (dynamicHeaderCodeLenSymsRestBits restBits)
            (dynamicHeaderCodeLenSymsRestLen restLen))
          hbit30 := by
    rw [dynamicCodeLenLensAfterReader, dynamicCodeLenLensReaderAt]
    dsimp [bw30, bitsTot]
    apply BitReader.ext
    · exact hfull30Flush.symm
    · simp [BitWriter.readerAt]
    · simp [BitWriter.readerAt]
  have hfinish0 :=
    finishDynamicTablesAfterCodeLenLengths_readerAt_writeBits
      (bw := bw30) (restBits := restBits) (restLen := restLen) hbit30 hcur30
  have hfinish :
      finishDynamicTablesAfterCodeLenLengths (dynamicCodeLenLensAfterReader bw restBits restLen hbit) =
        some
          (fixedLitLenHuffman, fixedDistHuffman,
            dynamicTablesAfterHeaderReaderAt bw restBits restLen hbit) := by
    rw [hbr30Start]
    simpa [dynamicTablesAfterHeaderReaderAt, dynamicCodeLenSymsReaderAt, bw30] using hfinish0
  calc
    readDynamicTablesAfterHeader br =
        finishDynamicTablesAfterCodeLenLengths (dynamicCodeLenLensAfterReader bw restBits restLen hbit) := by
          exact readDynamicTablesAfterHeader_eq_finish hreadLens hmkCodeLen
    _ = some
          (fixedLitLenHuffman, fixedDistHuffman,
            dynamicTablesAfterHeaderReaderAt bw restBits restLen hbit) := hfinish

end Png

end Bitmaps
