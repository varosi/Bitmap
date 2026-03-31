import Bitmap.Lemmas.Png.FixedBlockProofsCommon
import Bitmap.Lemmas.Png.FixedBlockProofsDecode
import Bitmap.Lemmas.Png.FixedBlockProofsScanBase

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_match3_dist1_readerAt_writeBits
    (fuel : Nat) (bw : BitWriter) (tailBits tailLen : Nat) (out : ByteArray)
    (hout : 0 < out.size) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let info := fixedLenMatchInfo 3
    let sym := info.1
    let extraBits := info.2.1
    let extraLen := info.2.2
    let codeLen := fixedLitLenCode sym
    let symBits := reverseBits codeLen.1 codeLen.2
    let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
    let distLenTot := 5 + tailLen
    let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
    let lenLenTot := extraLen + distLenTot
    let bitsTot := symBits ||| (lenBitsTot <<< codeLen.2)
    let lenTot := codeLen.2 + lenLenTot
    let bwAll := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bwAll.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedBlockFuelFast (fuel + 1) br0 out =
      let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
      let bw2 := BitWriter.writeBits bw1 lenBitsTot extraLen
      let bwDistAll := BitWriter.writeBits bw2 distBitsTot distLenTot
      let brAfter := BitWriter.readerAt (BitWriter.writeBits bw2 distBitsTot 5) bwDistAll.flush
        (by
          have hk : 5 ≤ distLenTot := by omega
          simpa [distLenTot] using (flush_size_writeBits_prefix bw2 distBitsTot 5 distLenTot hk))
        (bitPos_lt_8_writeBits bw2 distBitsTot 5 (bitPos_lt_8_writeBits bw1 lenBitsTot extraLen
          (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit)))
      decodeFixedBlockFuelFast fuel brAfter (pushRepeat out (out.get! (out.size - 1)) 3) := by
  have hlen : 3 ≤ 3 ∧ 3 ≤ 258 := by constructor <;> decide
  simpa [fixedLenMatchInfo_three] using
    (decodeFixedBlockFuelFast_step_fixedLenMatchInfo_dist1_readerAt_writeBits
      (fuel := fuel) (bw := bw) (matchLen := 3) (tailBits := tailBits) (tailLen := tailLen)
      (out := out) (hlen := hlen) (hout := hout) (hbit := hbit) (hcur := hcur))

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_dist1Run3_readerAt_writeBits
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (out : ByteArray)
    (_hout : 0 < out.size) (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsLen := dist1RunBitsTail b 3 tailBits tailLen
    let bitsTot := bitsLen.1
    let lenTot := bitsLen.2
    let bwAll := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bwAll.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    ∃ brAfter,
      decodeFixedBlockFuelFast (fuel + dist1RunSteps 3) br0 out =
        decodeFixedBlockFuelFast fuel brAfter (dist1RunOut out b 3) := by
  -- Existing theorem already gives this specialized existential; keep a named wrapper for `remaining = 3`.
  simpa using
    (decodeFixedBlockFuelFast_dist1Run_readerAt_writeBits_exists
      (fuel := fuel) (bw := bw) (b := b) (remaining := 3) (tailBits := tailBits) (tailLen := tailLen)
      (out := out) (htail2 := htail2) (hbit := hbit) (hcur := hcur))

def match3Dist1AfterReader (bw : BitWriter) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let info := fixedLenMatchInfo 3
  let sym := info.1
  let extraBits := info.2.1
  let extraLen := info.2.2
  let codeLen := fixedLitLenCode sym
  let symBits := reverseBits codeLen.1 codeLen.2
  let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
  let distLenTot := 5 + tailLen
  let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
  let bwM1 := BitWriter.writeBits bw (symBits ||| (lenBitsTot <<< codeLen.2)) codeLen.2
  let bwM2 := BitWriter.writeBits bwM1 lenBitsTot extraLen
  let bwDistAll := BitWriter.writeBits bwM2 distBitsTot distLenTot
  BitWriter.readerAt (BitWriter.writeBits bwM2 distBitsTot 5) bwDistAll.flush
    (by
      have hk : 5 ≤ distLenTot := by omega
      simpa [distLenTot] using (flush_size_writeBits_prefix bwM2 distBitsTot 5 distLenTot hk))
    (bitPos_lt_8_writeBits bwM2 distBitsTot 5
      (bitPos_lt_8_writeBits bwM1 lenBitsTot extraLen
        (bitPos_lt_8_writeBits bw
          (symBits ||| (lenBitsTot <<< codeLen.2)) codeLen.2 hbit)))

def match3Dist1TailWriter (bw : BitWriter) (tailBits _tailLen : Nat) : BitWriter :=
  let info := fixedLenMatchInfo 3
  let sym := info.1
  let extraBits := info.2.1
  let extraLen := info.2.2
  let codeLen := fixedLitLenCode sym
  let symBits := reverseBits codeLen.1 codeLen.2
  let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
  let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
  let bwM1 := BitWriter.writeBits bw (symBits ||| (lenBitsTot <<< codeLen.2)) codeLen.2
  let bwM2 := BitWriter.writeBits bwM1 lenBitsTot extraLen
  BitWriter.writeBits bwM2 distBitsTot 5

lemma match3Dist1TailWriter_bitPos_lt
    (bw : BitWriter) (tailBits tailLen : Nat) (hbit : bw.bitPos < 8) :
    (match3Dist1TailWriter bw tailBits tailLen).bitPos < 8 := by
  dsimp [match3Dist1TailWriter]
  repeat
    first | apply bitPos_lt_8_writeBits
  exact hbit

lemma match3Dist1TailWriter_curClearAbove
    (bw : BitWriter) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (match3Dist1TailWriter bw tailBits tailLen).curClearAbove := by
  dsimp [match3Dist1TailWriter]
  repeat
    first | apply curClearAbove_writeBits | apply bitPos_lt_8_writeBits | assumption

def match3Dist1TailStartReader (bw : BitWriter) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bwTail := match3Dist1TailWriter bw tailBits tailLen
  BitWriter.readerAt bwTail (BitWriter.writeBits bwTail tailBits tailLen).flush
    (flush_size_writeBits_le bwTail tailBits tailLen)
    (match3Dist1TailWriter_bitPos_lt bw tailBits tailLen hbit)

set_option maxRecDepth 200000 in
lemma match3Dist1AfterReader_eq_tailStartReader
    (bw : BitWriter) (tailBits tailLen : Nat) (hbit : bw.bitPos < 8) :
    match3Dist1AfterReader bw tailBits tailLen hbit =
      match3Dist1TailStartReader bw tailBits tailLen hbit := by
  let info := fixedLenMatchInfo 3
  let sym := info.1
  let extraBits := info.2.1
  let extraLen := info.2.2
  let codeLen := fixedLitLenCode sym
  let symBits := reverseBits codeLen.1 codeLen.2
  let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
  let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
  let bwM1 := BitWriter.writeBits bw (symBits ||| (lenBitsTot <<< codeLen.2)) codeLen.2
  let bwM2 := BitWriter.writeBits bwM1 lenBitsTot extraLen
  have hbit2 : bwM2.bitPos < 8 := by
    dsimp [bwM2]
    exact bitPos_lt_8_writeBits bwM1 lenBitsTot extraLen
      (bitPos_lt_8_writeBits bw (symBits ||| (lenBitsTot <<< codeLen.2)) codeLen.2 hbit)
  have hreader :=
    readerAt_writeBits_dist1Prefix_concat (bw2 := bwM2) (tailBits := tailBits) (tailLen := tailLen)
      (hbit2 := hbit2)
  simpa [match3Dist1AfterReader, match3Dist1TailStartReader, match3Dist1TailWriter,
    info, sym, extraBits, extraLen, codeLen, symBits, distBitsTot, lenBitsTot, bwM1, bwM2]
    using hreader

def match3Dist1StartReader (bw : BitWriter) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let info := fixedLenMatchInfo 3
  let sym := info.1
  let extraBits := info.2.1
  let extraLen := info.2.2
  let codeLen := fixedLitLenCode sym
  let symBits := reverseBits codeLen.1 codeLen.2
  let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
  let distLenTot := 5 + tailLen
  let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
  let lenLenTot := extraLen + distLenTot
  let bitsTot := symBits ||| (lenBitsTot <<< codeLen.2)
  let lenTot := codeLen.2 + lenLenTot
  BitWriter.readerAt bw
    (BitWriter.writeBits bw bitsTot lenTot).flush
    (flush_size_writeBits_le bw bitsTot lenTot) hbit

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_match3Dist1_readerAt_writeBits
    (fuel : Nat) (bw : BitWriter) (tailBits tailLen : Nat) (out : ByteArray)
    (hout : 0 < out.size) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedBlockFuelFast (fuel + 1) (match3Dist1StartReader bw tailBits tailLen hbit) out =
      decodeFixedBlockFuelFast fuel (match3Dist1AfterReader bw tailBits tailLen hbit)
        (pushRepeat out (out.get! (out.size - 1)) 3) := by
  simpa [match3Dist1StartReader, match3Dist1AfterReader] using
    (decodeFixedBlockFuelFast_step_match3_dist1_readerAt_writeBits
      (fuel := fuel) (bw := bw) (tailBits := tailBits) (tailLen := tailLen)
      (out := out) (hout := hout) (hbit := hbit) (hcur := hcur))

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_match3Dist1_readerAt_writeBits_tail
    (fuel : Nat) (bw : BitWriter) (tailBits tailLen : Nat) (out : ByteArray)
    (hout : 0 < out.size) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedBlockFuelFast (fuel + 1) (match3Dist1StartReader bw tailBits tailLen hbit) out =
      decodeFixedBlockFuelFast fuel (match3Dist1TailStartReader bw tailBits tailLen hbit)
        (pushRepeat out (out.get! (out.size - 1)) 3) := by
  rw [← match3Dist1AfterReader_eq_tailStartReader
    (bw := bw) (tailBits := tailBits) (tailLen := tailLen) (hbit := hbit)]
  exact decodeFixedBlockFuelFast_match3Dist1_readerAt_writeBits
    (fuel := fuel) (bw := bw) (tailBits := tailBits) (tailLen := tailLen)
    (out := out) (hout := hout) (hbit := hbit) (hcur := hcur)

def literalThenMatch3Dist1StartReader (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bitsLen := dist1RunBitsTail b 3 tailBits tailLen
  BitWriter.readerAt bw (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
    (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit

def literalThenMatch3Dist1MidReader (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let chunkBits := dist1ChunkLoopBitsTail 3 tailBits tailLen
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (chunkBits.1 <<< codeLen.2)
  let lenTot := codeLen.2 + chunkBits.2
  let bwAll := BitWriter.writeBits bw bitsTot lenTot
  let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
  BitWriter.readerAt bw1 bwAll.flush
    (by
      have hk : codeLen.2 ≤ lenTot := by omega
      simpa [bwAll, lenTot] using (flush_size_writeBits_prefix bw bitsTot codeLen.2 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit)

def literalThenMatch3Dist1AfterReader (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  match3Dist1AfterReader (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen
    (by
      simpa [writeFixedLiteralFast_eq_writeBits] using
        (bitPos_lt_8_writeBits bw
          (reverseBits (fixedLitLenCode b.toNat).1 (fixedLitLenCode b.toNat).2)
          (fixedLitLenCode b.toNat).2 hbit))

def literalThenMatch3Dist1TailWriter (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) : BitWriter :=
  (BitWriter.writeFixedLiteralFast bw b).writeFixedMatchDist1Fast 3

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma literalThenMatch3Dist1TailWriter_bitPos_lt
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (hbit : bw.bitPos < 8) :
    (literalThenMatch3Dist1TailWriter bw b tailBits tailLen).bitPos < 8 := by
  let bw1 := BitWriter.writeFixedLiteralFast bw b
  let matchCode := fixedLitLenCode 257
  let matchBits := reverseBits matchCode.1 matchCode.2
  have hbitLit : bw1.bitPos < 8 := by
    let litCode := fixedLitLenCode b.toNat
    let litBits := reverseBits litCode.1 litCode.2
    simpa [bw1, litCode, litBits] using
      (bitPos_lt_8_writeBits bw litBits litCode.2 hbit)
  have hbitMatch : (BitWriter.writeBits bw1 matchBits matchCode.2).bitPos < 8 := by
    exact bitPos_lt_8_writeBits bw1 matchBits matchCode.2 hbitLit
  have hbitFinal :
      (BitWriter.writeBits (BitWriter.writeBits bw1 matchBits matchCode.2) 0 5).bitPos < 8 := by
    exact bitPos_lt_8_writeBits (BitWriter.writeBits bw1 matchBits matchCode.2) 0 5 hbitMatch
  unfold literalThenMatch3Dist1TailWriter
  change (bw1.writeFixedMatchDist1Fast 3).bitPos < 8
  rw [writeFixedMatchDist1Fast_eq_writeBits_chain (bw := bw1) (matchLen := 3) (hlen := by decide)]
  simpa [bw1, matchCode, matchBits, fixedLenMatchInfo_three, writeBits_zero] using hbitFinal

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma literalThenMatch3Dist1TailWriter_curClearAbove
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (literalThenMatch3Dist1TailWriter bw b tailBits tailLen).curClearAbove := by
  let bw1 := BitWriter.writeFixedLiteralFast bw b
  let litCode := fixedLitLenCode b.toNat
  let litBits := reverseBits litCode.1 litCode.2
  let matchCode := fixedLitLenCode 257
  let matchBits := reverseBits matchCode.1 matchCode.2
  have hbitLit : bw1.bitPos < 8 := by
    simpa [bw1, litCode, litBits] using
      (bitPos_lt_8_writeBits bw litBits litCode.2 hbit)
  have hcurLit : bw1.curClearAbove := by
    simpa [bw1, litCode, litBits] using
      (curClearAbove_writeBits bw litBits litCode.2 hbit hcur)
  have hbitMatch : (BitWriter.writeBits bw1 matchBits matchCode.2).bitPos < 8 := by
    exact bitPos_lt_8_writeBits bw1 matchBits matchCode.2 hbitLit
  have hcurMatch : (BitWriter.writeBits bw1 matchBits matchCode.2).curClearAbove := by
    exact curClearAbove_writeBits bw1 matchBits matchCode.2 hbitLit hcurLit
  have hcurFinal :
      (BitWriter.writeBits (BitWriter.writeBits bw1 matchBits matchCode.2) 0 5).curClearAbove := by
    exact curClearAbove_writeBits (BitWriter.writeBits bw1 matchBits matchCode.2) 0 5 hbitMatch hcurMatch
  unfold literalThenMatch3Dist1TailWriter
  change (bw1.writeFixedMatchDist1Fast 3).curClearAbove
  rw [writeFixedMatchDist1Fast_eq_writeBits_chain (bw := bw1) (matchLen := 3) (hlen := by decide)]
  simpa [bw1, matchCode, matchBits, fixedLenMatchInfo_three, writeBits_zero] using hcurFinal

private lemma writeFixedLiteralFast_bitPos_lt
    (bw : BitWriter) (b : UInt8) (hbit : bw.bitPos < 8) :
    (BitWriter.writeFixedLiteralFast bw b).bitPos < 8 := by
  simpa [writeFixedLiteralFast_eq_writeBits] using
    (bitPos_lt_8_writeBits bw
      (reverseBits (fixedLitLenCode b.toNat).1 (fixedLitLenCode b.toNat).2)
      (fixedLitLenCode b.toNat).2 hbit)

private lemma writeFixedLiteralFast_curClearAbove
    (bw : BitWriter) (b : UInt8) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (BitWriter.writeFixedLiteralFast bw b).curClearAbove := by
  simpa [writeFixedLiteralFast_eq_writeBits] using
    (curClearAbove_writeBits bw
      (reverseBits (fixedLitLenCode b.toNat).1 (fixedLitLenCode b.toNat).2)
      (fixedLitLenCode b.toNat).2 hbit hcur)

def literalThenMatch3Dist1TailStartReader (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  match3Dist1TailStartReader (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen
    (writeFixedLiteralFast_bitPos_lt bw b hbit)

private lemma literalThenMatch3Dist1AfterReader_eq_tailStartReader
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (hbit : bw.bitPos < 8) :
    literalThenMatch3Dist1AfterReader bw b tailBits tailLen hbit =
      literalThenMatch3Dist1TailStartReader bw b tailBits tailLen hbit := by
  simpa [literalThenMatch3Dist1AfterReader, literalThenMatch3Dist1TailStartReader] using
    (match3Dist1AfterReader_eq_tailStartReader
      (bw := BitWriter.writeFixedLiteralFast bw b)
      (tailBits := tailBits) (tailLen := tailLen)
      (hbit := writeFixedLiteralFast_bitPos_lt bw b hbit))

private lemma literalThenMatch3Dist1MidReader_eq_match3Dist1StartReader
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (hbit : bw.bitPos < 8) :
    literalThenMatch3Dist1MidReader bw b tailBits tailLen hbit =
      match3Dist1StartReader (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen
        (writeFixedLiteralFast_bitPos_lt bw b hbit) := by
  let chunkBits := dist1ChunkLoopBitsTail 3 tailBits tailLen
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (chunkBits.1 <<< codeLen.2)
  let lenTot := codeLen.2 + chunkBits.2
  let bwAll := BitWriter.writeBits bw bitsTot lenTot
  let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
  have hbitsLt : bits < 2 ^ codeLen.2 := by
    simpa [bits] using (reverseBits_lt codeLen.1 codeLen.2)
  have hconcat :
      BitWriter.writeBits bw bitsTot lenTot =
        BitWriter.writeBits (BitWriter.writeBits bw bits codeLen.2) chunkBits.1 chunkBits.2 := by
    simpa [bitsTot, lenTot] using
      (writeBits_concat bw bits chunkBits.1 codeLen.2 chunkBits.2 hbitsLt)
  have hmod : bitsTot % 2 ^ codeLen.2 = bits := by
    have hmod' : bitsTot % 2 ^ codeLen.2 = bits % 2 ^ codeLen.2 := by
      simpa [bitsTot] using
        (mod_two_pow_or_shift (a := bits) (b := chunkBits.1) (k := codeLen.2) (len := codeLen.2)
          (hk := le_rfl))
    have hbitsMod : bits % 2 ^ codeLen.2 = bits := Nat.mod_eq_of_lt hbitsLt
    simpa [hbitsMod] using hmod'
  have hwriteBits :
      BitWriter.writeBits bw bitsTot codeLen.2 = BitWriter.writeBits bw bits codeLen.2 := by
    calc
      BitWriter.writeBits bw bitsTot codeLen.2
          = BitWriter.writeBits bw (bitsTot % 2 ^ codeLen.2) codeLen.2 := by
              simpa using (writeBits_mod bw bitsTot codeLen.2)
      _ = BitWriter.writeBits bw bits codeLen.2 := by
            simp [hmod]
  have hbw1 :
      bw1 = BitWriter.writeFixedLiteralFast bw b := by
    calc
      bw1 = BitWriter.writeBits bw bitsTot codeLen.2 := by rfl
      _ = BitWriter.writeBits bw bits codeLen.2 := hwriteBits
      _ = BitWriter.writeFixedLiteralFast bw b := by
            simpa [codeLen, bits] using
              (writeFixedLiteralFast_eq_writeBits (bw := bw) (b := b)).symm
  have hbit1 : bw1.bitPos < 8 := by
    exact bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit
  have hbwAll :
      bwAll = BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) chunkBits.1 chunkBits.2 := by
    calc
      bwAll = BitWriter.writeBits bw1 chunkBits.1 chunkBits.2 := by
        dsimp [bwAll, bw1]
        simpa [hwriteBits] using hconcat
      _ = BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) chunkBits.1 chunkBits.2 := by
        simpa [hbw1]
  have hMidChunk :
      literalThenMatch3Dist1MidReader bw b tailBits tailLen hbit =
        BitWriter.readerAt bw1 (BitWriter.writeBits bw1 chunkBits.1 chunkBits.2).flush
          (flush_size_writeBits_le bw1 chunkBits.1 chunkBits.2) hbit1 := by
    apply BitReader.ext
    · change (BitWriter.writeBits bw bitsTot lenTot).flush =
          (BitWriter.writeBits bw1 chunkBits.1 chunkBits.2).flush
      simpa [bwAll] using congrArg BitWriter.flush (show bwAll = BitWriter.writeBits bw1 chunkBits.1 chunkBits.2 from by
        calc
          bwAll = BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) chunkBits.1 chunkBits.2 := hbwAll
          _ = BitWriter.writeBits bw1 chunkBits.1 chunkBits.2 := by simpa [hbw1])
    · change (BitWriter.writeBits bw bitsTot codeLen.2).out.size = bw1.out.size
      simpa [bw1] using congrArg BitWriter.out hwriteBits
    · change (BitWriter.writeBits bw bitsTot codeLen.2).bitPos = bw1.bitPos
      simpa [bw1] using congrArg BitWriter.bitPos hwriteBits
  have hTailReader :
      BitWriter.readerAt bw1 (BitWriter.writeBits bw1 chunkBits.1 chunkBits.2).flush
          (flush_size_writeBits_le bw1 chunkBits.1 chunkBits.2) hbit1 =
        BitWriter.readerAt (BitWriter.writeFixedLiteralFast bw b)
          (BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) chunkBits.1 chunkBits.2).flush
          (flush_size_writeBits_le (BitWriter.writeFixedLiteralFast bw b) chunkBits.1 chunkBits.2)
          (writeFixedLiteralFast_bitPos_lt bw b hbit) := by
    apply BitReader.ext
    · simpa [hbw1] using
        congrArg BitWriter.flush
          (congrArg (fun bw' => BitWriter.writeBits bw' chunkBits.1 chunkBits.2) hbw1)
    · simpa using congrArg (fun bw' => bw'.out.size) hbw1
    · simpa using congrArg BitWriter.bitPos hbw1
  calc
    literalThenMatch3Dist1MidReader bw b tailBits tailLen hbit
        = BitWriter.readerAt bw1 (BitWriter.writeBits bw1 chunkBits.1 chunkBits.2).flush
            (flush_size_writeBits_le bw1 chunkBits.1 chunkBits.2) hbit1 := hMidChunk
    _ = BitWriter.readerAt (BitWriter.writeFixedLiteralFast bw b)
          (BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) chunkBits.1 chunkBits.2).flush
          (flush_size_writeBits_le (BitWriter.writeFixedLiteralFast bw b) chunkBits.1 chunkBits.2)
          (writeFixedLiteralFast_bitPos_lt bw b hbit) := hTailReader
    _ = match3Dist1StartReader (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen
          (writeFixedLiteralFast_bitPos_lt bw b hbit) := by
            simp [match3Dist1StartReader, chunkBits]

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_literalThenMatch3Dist1_readerAt_writeBits_exists
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (out : ByteArray)
    (hout : 0 < out.size) (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    ∃ brAfter,
      decodeFixedBlockFuelFast (fuel + 2) (literalThenMatch3Dist1StartReader bw b tailBits tailLen hbit) out =
        decodeFixedBlockFuelFast fuel brAfter (dist1RunOut out b 3) := by
  -- compact wrapper over the existing `remaining = 3` dist1-run theorem
  have h := decodeFixedBlockFuelFast_dist1Run3_readerAt_writeBits
    (fuel := fuel) (bw := bw) (b := b) (tailBits := tailBits) (tailLen := tailLen)
    (out := out) (_hout := hout) (htail2 := htail2) (hbit := hbit) (hcur := hcur)
  simpa [literalThenMatch3Dist1StartReader, dist1RunSteps_three, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_literalThenMatch3Dist1_readerAt_writeBits
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (out : ByteArray)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedBlockFuelFast (fuel + 2) (literalThenMatch3Dist1StartReader bw b tailBits tailLen hbit) out =
      decodeFixedBlockFuelFast fuel (literalThenMatch3Dist1AfterReader bw b tailBits tailLen hbit)
        (dist1RunOut out b 3) := by
  let chunkBits := dist1ChunkLoopBitsTail 3 tailBits tailLen
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (chunkBits.1 <<< codeLen.2)
  let lenTot := codeLen.2 + chunkBits.2
  let bwAll := BitWriter.writeBits bw bitsTot lenTot
  let brMid := literalThenMatch3Dist1MidReader bw b tailBits tailLen hbit
  have htail2Chunk : 2 ≤ chunkBits.2 := by
    exact le_trans htail2 (dist1ChunkLoopBitsTail_len_ge 3 tailBits tailLen)
  have hLit :=
    decodeFixedBlockFuelFast_step_literal_readerAt_writeBits
      (fuel := fuel + 1) (bw := bw) (b := b)
      (tailBits := chunkBits.1) (tailLen := chunkBits.2)
      (out := out) (htail2 := htail2Chunk) (hbit := hbit) (hcur := hcur)
  have hLitStep :
      decodeFixedBlockFuelFast (fuel + 2) (literalThenMatch3Dist1StartReader bw b tailBits tailLen hbit) out =
        decodeFixedBlockFuelFast (fuel + 1) (literalThenMatch3Dist1MidReader bw b tailBits tailLen hbit)
          (out.push b) := by
    simpa [literalThenMatch3Dist1StartReader, literalThenMatch3Dist1MidReader, dist1RunBitsTail_three,
      chunkBits, codeLen, bits, bitsTot, lenTot, bwAll, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hLit
  have hlast : (out.push b).get! ((out.push b).size - 1) = b := by
    simpa using get!_last_push out b
  have hpush :
      pushRepeat (out.push b) ((out.push b).get! ((out.push b).size - 1)) 3 = dist1RunOut out b 3 := by
    calc
      pushRepeat (out.push b) ((out.push b).get! ((out.push b).size - 1)) 3
          = pushRepeat (out.push b) b 3 := by
              exact congrArg (fun x => pushRepeat (out.push b) x 3) hlast
      _ = dist1RunOut out b 3 := by simp [dist1RunOut]
  have hMidEq :
      brMid =
        match3Dist1StartReader (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen
          (writeFixedLiteralFast_bitPos_lt bw b hbit) := by
    exact literalThenMatch3Dist1MidReader_eq_match3Dist1StartReader
      (bw := bw) (b := b) (tailBits := tailBits) (tailLen := tailLen) (hbit := hbit)
  have hMatchTail :
      decodeFixedBlockFuelFast (fuel + 1) brMid (out.push b) =
        decodeFixedBlockFuelFast fuel (literalThenMatch3Dist1TailStartReader bw b tailBits tailLen hbit)
          (dist1RunOut out b 3) := by
    rw [hMidEq]
    have hMatch :=
      decodeFixedBlockFuelFast_match3Dist1_readerAt_writeBits_tail
        (fuel := fuel) (bw := BitWriter.writeFixedLiteralFast bw b)
        (tailBits := tailBits) (tailLen := tailLen)
        (out := out.push b) (hout := by simp [ByteArray.size_push])
        (hbit := writeFixedLiteralFast_bitPos_lt bw b hbit)
        (hcur := writeFixedLiteralFast_curClearAbove bw b hbit hcur)
    simpa only [literalThenMatch3Dist1TailStartReader, hpush] using hMatch
  have hTail :
      decodeFixedBlockFuelFast (fuel + 2) (literalThenMatch3Dist1StartReader bw b tailBits tailLen hbit) out =
        decodeFixedBlockFuelFast fuel (literalThenMatch3Dist1TailStartReader bw b tailBits tailLen hbit)
          (dist1RunOut out b 3) := by
    exact hLitStep.trans (by simpa [brMid] using hMatchTail)
  rw [literalThenMatch3Dist1AfterReader_eq_tailStartReader
    (bw := bw) (b := b) (tailBits := tailBits) (tailLen := tailLen) (hbit := hbit)]
  exact hTail

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_literalThenMatch3Dist1_readerAt_writeBits_tail
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (out : ByteArray)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedBlockFuelFast (fuel + 2) (literalThenMatch3Dist1StartReader bw b tailBits tailLen hbit) out =
      decodeFixedBlockFuelFast fuel (literalThenMatch3Dist1TailStartReader bw b tailBits tailLen hbit)
        (dist1RunOut out b 3) := by
  have hmain :=
    decodeFixedBlockFuelFast_literalThenMatch3Dist1_readerAt_writeBits
      (fuel := fuel) (bw := bw) (b := b) (tailBits := tailBits) (tailLen := tailLen)
      (out := out) (htail2 := htail2) (hbit := hbit) (hcur := hcur)
  rw [literalThenMatch3Dist1AfterReader_eq_tailStartReader
    (bw := bw) (b := b) (tailBits := tailBits) (tailLen := tailLen) (hbit := hbit)] at hmain
  exact hmain

@[irreducible] def fixedQuadStartReader (data : Array UInt8) (i : Nat) (bw : BitWriter)
    (hbit : bw.bitPos < 8) : BitReader :=
  BitWriter.readerAt bw
    (BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2).flush
    (flush_size_writeBits_le bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2) hbit

@[irreducible] def fixedQuadAfterReader (data : Array UInt8) (i : Nat) (bw : BitWriter)
    (hbit : bw.bitPos < 8) : BitReader :=
  flushReader
    (BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2)
    (bitPos_lt_8_writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2 hbit)

@[irreducible] def fixedQuadQuadTailBits (data : Array UInt8) (i : Nat) : Nat :=
  (fixedQuadBitsEob data (i + 4)).1

@[irreducible] def fixedQuadQuadTailLen (data : Array UInt8) (i : Nat) : Nat :=
  (fixedQuadBitsEob data (i + 4)).2

@[irreducible] def fixedQuadLiteralTailBits (data : Array UInt8) (i : Nat) : Nat :=
  (fixedQuadBitsEob data (i + 1)).1

@[irreducible] def fixedQuadLiteralTailLen (data : Array UInt8) (i : Nat) : Nat :=
  (fixedQuadBitsEob data (i + 1)).2

@[irreducible] def fixedQuadQuadTailWriter
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8) : BitWriter :=
  literalThenMatch3Dist1TailWriter bw b (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i)

@[irreducible] def fixedQuadLiteralTailWriter
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8) : BitWriter :=
  literalTailWriter bw b (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)

private lemma fixedQuadQuadTailWriter_bitPos_lt
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) :
    (fixedQuadQuadTailWriter data i bw b).bitPos < 8 := by
  simpa [fixedQuadQuadTailWriter, fixedQuadQuadTailBits, fixedQuadQuadTailLen] using
    literalThenMatch3Dist1TailWriter_bitPos_lt bw b (fixedQuadQuadTailBits data i)
      (fixedQuadQuadTailLen data i) hbit

private lemma fixedQuadQuadTailWriter_curClearAbove
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (fixedQuadQuadTailWriter data i bw b).curClearAbove := by
  simpa [fixedQuadQuadTailWriter, fixedQuadQuadTailBits, fixedQuadQuadTailLen] using
    literalThenMatch3Dist1TailWriter_curClearAbove bw b (fixedQuadQuadTailBits data i)
      (fixedQuadQuadTailLen data i) hbit hcur

private lemma fixedQuadLiteralTailWriter_bitPos_lt
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) :
    (fixedQuadLiteralTailWriter data i bw b).bitPos < 8 := by
  simpa [fixedQuadLiteralTailWriter, fixedQuadLiteralTailBits, fixedQuadLiteralTailLen] using
    literalTailWriter_bitPos_lt bw b (fixedQuadLiteralTailBits data i)
      (fixedQuadLiteralTailLen data i) hbit

private lemma fixedQuadLiteralTailWriter_curClearAbove
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (fixedQuadLiteralTailWriter data i bw b).curClearAbove := by
  simpa [fixedQuadLiteralTailWriter, fixedQuadLiteralTailBits, fixedQuadLiteralTailLen] using
    literalTailWriter_curClearAbove bw b (fixedQuadLiteralTailBits data i)
      (fixedQuadLiteralTailLen data i) hbit hcur

@[irreducible] def fixedQuadQuadRecursiveBitPosLt
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) :
    (fixedQuadQuadTailWriter data i bw b).bitPos < 8 :=
  fixedQuadQuadTailWriter_bitPos_lt data i bw b hbit

private lemma fixedQuadQuadRecursiveCurClearAbove
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (fixedQuadQuadTailWriter data i bw b).curClearAbove :=
  fixedQuadQuadTailWriter_curClearAbove data i bw b hbit hcur

@[irreducible] def fixedQuadLiteralRecursiveBitPosLt
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) :
    (fixedQuadLiteralTailWriter data i bw b).bitPos < 8 :=
  fixedQuadLiteralTailWriter_bitPos_lt data i bw b hbit

private lemma fixedQuadLiteralRecursiveCurClearAbove
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (fixedQuadLiteralTailWriter data i bw b).curClearAbove :=
  fixedQuadLiteralTailWriter_curClearAbove data i bw b hbit hcur

@[irreducible] def fixedQuadQuadTailStartReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) : BitReader :=
  literalThenMatch3Dist1TailStartReader bw b (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i) hbit

@[irreducible] def fixedQuadQuadTailAfterReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) : BitReader :=
  flushReader
    (BitWriter.writeBits (fixedQuadQuadTailWriter data i bw b)
      (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i))
    (bitPos_lt_8_writeBits (fixedQuadQuadTailWriter data i bw b)
      (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i)
      (fixedQuadQuadTailWriter_bitPos_lt data i bw b hbit))

@[irreducible] def fixedQuadLiteralTailStartReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) : BitReader :=
  literalTailStartReader bw b (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i) hbit

@[irreducible] def fixedQuadLiteralTailAfterReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) : BitReader :=
  flushReader
    (BitWriter.writeBits (fixedQuadLiteralTailWriter data i bw b)
      (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i))
    (bitPos_lt_8_writeBits (fixedQuadLiteralTailWriter data i bw b)
      (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)
      (fixedQuadLiteralTailWriter_bitPos_lt data i bw b hbit))

@[irreducible] def fixedQuadQuadRecursiveStartReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) : BitReader :=
  fixedQuadStartReader data (i + 4) (fixedQuadQuadTailWriter data i bw b)
    (fixedQuadQuadRecursiveBitPosLt data i bw b hbit)

@[irreducible] def fixedQuadQuadRecursiveAfterReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) : BitReader :=
  fixedQuadAfterReader data (i + 4) (fixedQuadQuadTailWriter data i bw b)
    (fixedQuadQuadRecursiveBitPosLt data i bw b hbit)

@[irreducible] def fixedQuadLiteralRecursiveStartReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) : BitReader :=
  fixedQuadStartReader data (i + 1) (fixedQuadLiteralTailWriter data i bw b)
    (fixedQuadLiteralRecursiveBitPosLt data i bw b hbit)

@[irreducible] def fixedQuadLiteralRecursiveAfterReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) : BitReader :=
  fixedQuadAfterReader data (i + 1) (fixedQuadLiteralTailWriter data i bw b)
    (fixedQuadLiteralRecursiveBitPosLt data i bw b hbit)

private lemma match3Dist1TailWriter_eq_writeFixedMatchDist1Fast_three
    (bw : BitWriter) (tailBits _tailLen : Nat) :
    match3Dist1TailWriter bw tailBits _tailLen = BitWriter.writeFixedMatchDist1Fast bw 3 := by
  have hcode : fixedLitLenCode 257 = (1, 7) := by
    simpa using fixedLitLenCode_hi 257 (by decide) (by decide)
  have hsym : reverseBits 1 7 = 64 := by native_decide
  let distBitsTot := tailBits <<< 5
  have hmod1 : (64 ||| (distBitsTot <<< 7)) % 2 ^ 7 = 64 := by
    have hmod' := mod_two_pow_or_shift (a := 64) (b := distBitsTot) (k := 7) (len := 7) (hk := le_rfl)
    simpa [distBitsTot] using hmod'
  have hwrite1 :
      BitWriter.writeBits bw (64 ||| (distBitsTot <<< 7)) 7 =
        BitWriter.writeBits bw 64 7 := by
    rw [writeBits_mod, hmod1]
  have hmod0 : distBitsTot % 2 ^ 5 = 0 := by
    simpa [distBitsTot] using
      (mod_two_pow_or_shift (a := 0) (b := tailBits) (k := 5) (len := 5) (hk := by decide))
  have hwrite3 :
      BitWriter.writeBits (BitWriter.writeBits bw 64 7) distBitsTot 5 =
        BitWriter.writeBits (BitWriter.writeBits bw 64 7) 0 5 := by
    rw [writeBits_mod, hmod0]
  calc
    match3Dist1TailWriter bw tailBits _tailLen
        = BitWriter.writeBits
            (BitWriter.writeBits bw (64 ||| (distBitsTot <<< 7)) 7) distBitsTot 5 := by
            simp [match3Dist1TailWriter, fixedLenMatchInfo_three, hcode, hsym, distBitsTot, writeBits_zero]
    _ = BitWriter.writeBits (BitWriter.writeBits bw 64 7) distBitsTot 5 := by
          simpa using congrArg (fun bw' => BitWriter.writeBits bw' distBitsTot 5) hwrite1
    _ = BitWriter.writeBits (BitWriter.writeBits bw 64 7) 0 5 := hwrite3
    _ = BitWriter.writeFixedMatchDist1Fast bw 3 := by
          symm
          rw [writeFixedMatchDist1Fast_eq_writeBits_chain (bw := bw) (matchLen := 3) (hlen := by decide)]
          simp [fixedLenMatchInfo_three, hcode, hsym, writeBits_zero]

set_option maxHeartbeats 0 in
private lemma fixedQuadQuadRecursiveStartReader_eq_fixedQuadQuadTailStartReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) :
    fixedQuadQuadRecursiveStartReader data i bw b hbit =
      fixedQuadQuadTailStartReader data i bw b hbit := by
  let tailBits := (fixedQuadBitsEob data (i + 4)).1
  let tailLen := (fixedQuadBitsEob data (i + 4)).2
  let bw0 := BitWriter.writeFixedLiteralFast bw b
  have htail :
      match3Dist1TailWriter bw0 tailBits tailLen =
        BitWriter.writeFixedMatchDist1Fast bw0 3 := by
    simpa [bw0, tailBits, tailLen] using
      (match3Dist1TailWriter_eq_writeFixedMatchDist1Fast_three
        (bw := bw0) (tailBits := tailBits) (_tailLen := tailLen))
  unfold fixedQuadQuadRecursiveStartReader fixedQuadQuadTailStartReader
    fixedQuadStartReader fixedQuadQuadTailWriter fixedQuadQuadTailBits fixedQuadQuadTailLen
    literalThenMatch3Dist1TailStartReader match3Dist1TailStartReader literalThenMatch3Dist1TailWriter
  dsimp [tailBits, tailLen, bw0] at htail ⊢
  apply BitReader.ext
  · simpa [BitWriter.readerAt] using
      congrArg BitWriter.flush
        (congrArg
          (fun bw' =>
            BitWriter.writeBits bw' (fixedQuadBitsEob data (i + 4)).1
              (fixedQuadBitsEob data (i + 4)).2)
          htail.symm)
  · simpa [BitWriter.readerAt] using
      congrArg (fun bw' => bw'.out.size) htail.symm
  · simpa [BitWriter.readerAt] using
      congrArg BitWriter.bitPos htail.symm

private lemma fixedQuadQuadRecursiveAfterReader_eq_fixedQuadQuadTailAfterReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) :
    fixedQuadQuadRecursiveAfterReader data i bw b hbit =
      fixedQuadQuadTailAfterReader data i bw b hbit := by
  simp [fixedQuadQuadRecursiveAfterReader, fixedQuadQuadTailAfterReader,
    fixedQuadAfterReader, fixedQuadQuadTailWriter, fixedQuadQuadTailBits, fixedQuadQuadTailLen,
    flushReader]

private lemma fixedQuadLiteralRecursiveStartReader_eq_fixedQuadLiteralTailStartReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) :
    fixedQuadLiteralRecursiveStartReader data i bw b hbit =
      fixedQuadLiteralTailStartReader data i bw b hbit := by
  simp [fixedQuadLiteralRecursiveStartReader, fixedQuadLiteralTailStartReader,
    fixedQuadStartReader, fixedQuadLiteralTailWriter, fixedQuadLiteralTailBits,
    fixedQuadLiteralTailLen, literalTailStartReader]

private lemma fixedQuadLiteralRecursiveAfterReader_eq_fixedQuadLiteralTailAfterReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8) :
    fixedQuadLiteralRecursiveAfterReader data i bw b hbit =
      fixedQuadLiteralTailAfterReader data i bw b hbit := by
  simp [fixedQuadLiteralRecursiveAfterReader, fixedQuadLiteralTailAfterReader,
    fixedQuadAfterReader, fixedQuadLiteralTailWriter, fixedQuadLiteralTailBits,
    fixedQuadLiteralTailLen, flushReader]

private lemma fixedQuadQuadTailAfterReader_eq_fixedQuadAfterReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8)
    (hbits :
      fixedQuadBitsEob data i =
        dist1RunBitsTail b 3 (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i)) :
    fixedQuadQuadTailAfterReader data i bw b hbit = fixedQuadAfterReader data i bw hbit := by
  have hbwEq :
      BitWriter.writeBits (fixedQuadQuadTailWriter data i bw b)
        (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i) =
        BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2 := by
    unfold fixedQuadQuadTailWriter
    simpa [literalThenMatch3Dist1TailWriter, fixedQuadQuadTailBits, fixedQuadQuadTailLen, hbits] using
      (writeBits_dist1RunBitsTail_three
        (bw := bw) (b := b)
        (tailBits := fixedQuadQuadTailBits data i)
        (tailLen := fixedQuadQuadTailLen data i)).symm
  apply BitReader.ext <;> simp [fixedQuadQuadTailAfterReader, fixedQuadAfterReader, flushReader, hbwEq]

private lemma fixedQuadLiteralTailAfterReader_eq_fixedQuadAfterReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8)
    (hbit : bw.bitPos < 8)
    (hbits :
      fixedQuadBitsEob data i =
        literalRepeatBitsTail b 1 (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)) :
    fixedQuadLiteralTailAfterReader data i bw b hbit = fixedQuadAfterReader data i bw hbit := by
  have hbwEq :
      BitWriter.writeBits (fixedQuadLiteralTailWriter data i bw b)
        (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i) =
        BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2 := by
    simpa [fixedQuadLiteralTailWriter, fixedQuadLiteralTailBits, fixedQuadLiteralTailLen, hbits] using
      (writeBits_literalRepeatBitsTail_one_helper
        (bw := bw) (b := b)
        (tailBits := fixedQuadLiteralTailBits data i)
        (tailLen := fixedQuadLiteralTailLen data i)).symm
  apply BitReader.ext <;> simp [fixedQuadLiteralTailAfterReader, fixedQuadAfterReader, flushReader, hbwEq]

lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_decode_of_quad_tail
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (b : UInt8) (hbit : bw.bitPos < 8)
    (hbits :
      fixedQuadBitsEob data i =
        dist1RunBitsTail b 3 (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i))
    (hsteps : fixedQuadStepsEob data i = 2 + fixedQuadStepsEob data (i + 4))
    (houtEq : fixedQuadOut data i out = fixedQuadOut data (i + 4) (dist1RunOut out b 3))
    (hstep :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4) + 2)
        (literalThenMatch3Dist1StartReader bw b
          (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i) hbit) out =
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
        (fixedQuadQuadTailStartReader data i bw b hbit)
        (dist1RunOut out b 3))
    (htail :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
        (fixedQuadQuadTailStartReader data i bw b hbit)
        (dist1RunOut out b 3) =
        some (fixedQuadAfterReader data i bw hbit,
          fixedQuadOut data (i + 4) (dist1RunOut out b 3))) :
    decodeFixedBlockFuelFast (fixedQuadStepsEob data i)
      (fixedQuadStartReader data i bw hbit) out =
      some (fixedQuadAfterReader data i bw hbit, fixedQuadOut data i out) := by
  have hstart :
      fixedQuadStartReader data i bw hbit =
        literalThenMatch3Dist1StartReader bw b
          (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i) hbit := by
    simp [fixedQuadStartReader, literalThenMatch3Dist1StartReader, hbits, dist1RunBitsTail_three]
  have hrootToTail :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data i)
        (fixedQuadStartReader data i bw hbit) out =
        decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
          (fixedQuadQuadTailStartReader data i bw b hbit)
          (dist1RunOut out b 3) := by
    rw [hstart]
    simpa [hsteps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
  rw [hrootToTail]
  simpa [houtEq] using htail

lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_decode_of_literal_tail
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (b : UInt8) (hbit : bw.bitPos < 8)
    (hbits :
      fixedQuadBitsEob data i =
        literalRepeatBitsTail b 1 (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i))
    (hsteps : fixedQuadStepsEob data i = 1 + fixedQuadStepsEob data (i + 1))
    (houtEq : fixedQuadOut data i out = fixedQuadOut data (i + 1) (out.push b))
    (hstep :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1) + 1)
        (BitWriter.readerAt bw
          (BitWriter.writeBits bw (literalRepeatBitsTail b 1
            (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)).1
            (literalRepeatBitsTail b 1
              (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)).2).flush
          (flush_size_writeBits_le bw
            (literalRepeatBitsTail b 1 (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)).1
            (literalRepeatBitsTail b 1 (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)).2)
            hbit) out =
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
        (fixedQuadLiteralTailStartReader data i bw b hbit) (out.push b))
    (htail :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
        (fixedQuadLiteralTailStartReader data i bw b hbit) (out.push b) =
        some (fixedQuadAfterReader data i bw hbit,
          fixedQuadOut data (i + 1) (out.push b))) :
    decodeFixedBlockFuelFast (fixedQuadStepsEob data i)
      (fixedQuadStartReader data i bw hbit) out =
      some (fixedQuadAfterReader data i bw hbit, fixedQuadOut data i out) := by
  have hrootToTail :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data i)
        (fixedQuadStartReader data i bw hbit) out =
        decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
          (fixedQuadLiteralTailStartReader data i bw b hbit) (out.push b) := by
    simpa [fixedQuadStartReader, fixedQuadLiteralTailStartReader, literalTailStartReader,
      hbits, hsteps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
  rw [hrootToTail]
  simpa [houtEq] using htail

private structure FixedQuadQuadBranchData
    (data : Array UInt8) (i : Nat) (out : ByteArray) (b : UInt8) where
  bitsEq :
    fixedQuadBitsEob data i =
      dist1RunBitsTail b 3 (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i)
  stepsEq : fixedQuadStepsEob data i = 2 + fixedQuadStepsEob data (i + 4)
  outEq : fixedQuadOut data i out = fixedQuadOut data (i + 4) (dist1RunOut out b 3)

private structure FixedQuadLiteralBranchData
    (data : Array UInt8) (i : Nat) (out : ByteArray) (b : UInt8) where
  bitsEq :
    fixedQuadBitsEob data i =
      literalRepeatBitsTail b 1 (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)
  stepsEq : fixedQuadStepsEob data i = 1 + fixedQuadStepsEob data (i + 1)
  outEq : fixedQuadOut data i out = fixedQuadOut data (i + 1) (out.push b)

private lemma fixedQuadBranchData_of_quad
    (data : Array UInt8) (i : Nat) (out : ByteArray) (b : UInt8)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hb : b = data[i]'h)
    (hq : quadTailEqb data i b h3 = true) :
    FixedQuadQuadBranchData data i out b := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [fixedQuadQuadTailBits, fixedQuadQuadTailLen, hb] using
      (fixedQuadBitsEob_of_quad (data := data) (i := i) (h := h) (h3 := h3)
        (hq := by simpa [hb] using hq))
  · have hsteps0 :=
      fixedQuadStepsEob_of_quad (data := data) (i := i) (h := h) (h3 := h3)
        (hq := by simpa [hb] using hq)
    simpa [fixedQuadQuadTailBits, fixedQuadQuadTailLen, dist1RunSteps_three,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsteps0
  · simpa [fixedQuadQuadTailBits, fixedQuadQuadTailLen, hb] using
      (fixedQuadOut_of_quad (data := data) (i := i) (out := out) (h := h) (h3 := h3)
        (hq := by simpa [hb] using hq))

private lemma fixedQuadBranchData_of_lit_hqFalse
    (data : Array UInt8) (i : Nat) (out : ByteArray) (b : UInt8)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hb : b = data[i]'h)
    (hq : quadTailEqb data i b h3 = false) :
    FixedQuadLiteralBranchData data i out b := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [fixedQuadLiteralTailBits, fixedQuadLiteralTailLen, hb] using
      (fixedQuadBitsEob_of_lit_hqFalse (data := data) (i := i) (h := h) (h3 := h3)
        (hq := by simpa [hb] using hq))
  · simpa [fixedQuadLiteralTailBits, fixedQuadLiteralTailLen, hb] using
      (fixedQuadStepsEob_of_lit_hqFalse (data := data) (i := i) (h := h) (h3 := h3)
        (hq := by simpa [hb] using hq))
  · simpa [fixedQuadLiteralTailBits, fixedQuadLiteralTailLen, hb] using
      (fixedQuadOut_of_lit_hqFalse (data := data) (i := i) (out := out) (h := h) (h3 := h3)
        (hq := by simpa [hb] using hq))

private lemma fixedQuadBranchData_of_lit_noh3
    (data : Array UInt8) (i : Nat) (out : ByteArray) (b : UInt8)
    (h : i < data.size) (h3 : ¬ i + 3 < data.size)
    (hb : b = data[i]'h) :
    FixedQuadLiteralBranchData data i out b := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [fixedQuadLiteralTailBits, fixedQuadLiteralTailLen, hb] using
      (fixedQuadBitsEob_of_lit_noh3 (data := data) (i := i) (h := h) (h3 := h3))
  · simpa [fixedQuadLiteralTailBits, fixedQuadLiteralTailLen, hb] using
      (fixedQuadStepsEob_of_lit_noh3 (data := data) (i := i) (h := h) (h3 := h3))
  · simpa [fixedQuadLiteralTailBits, fixedQuadLiteralTailLen, hb] using
      (fixedQuadOut_of_lit_noh3 (data := data) (i := i) (out := out) (h := h) (h3 := h3))

lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_exact_quad_branch
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (b : UInt8) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    (hbranch : FixedQuadQuadBranchData data i out b)
    (htail :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
        (fixedQuadQuadTailStartReader data i bw b hbit)
        (dist1RunOut out b 3) =
        some (fixedQuadQuadTailAfterReader data i bw b hbit,
          fixedQuadOut data (i + 4) (dist1RunOut out b 3))) :
    decodeFixedBlockFuelFast (fixedQuadStepsEob data i)
      (fixedQuadStartReader data i bw hbit) out =
      some (fixedQuadAfterReader data i bw hbit, fixedQuadOut data i out) := by
  have htail2 : 2 ≤ fixedQuadQuadTailLen data i := by
    simpa [fixedQuadQuadTailLen] using fixedQuadBitsEob_len_ge_two data (i + 4)
  have hstep :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4) + 2)
        (literalThenMatch3Dist1StartReader bw b
          (fixedQuadQuadTailBits data i) (fixedQuadQuadTailLen data i) hbit) out =
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
        (fixedQuadQuadTailStartReader data i bw b hbit)
        (dist1RunOut out b 3) := by
    simpa [fixedQuadQuadTailStartReader, fixedQuadQuadTailBits, fixedQuadQuadTailLen] using
      (decodeFixedBlockFuelFast_literalThenMatch3Dist1_readerAt_writeBits_tail
      (fuel := fixedQuadStepsEob data (i + 4)) (bw := bw) (b := b)
      (tailBits := fixedQuadQuadTailBits data i) (tailLen := fixedQuadQuadTailLen data i) (out := out)
      (htail2 := htail2) (hbit := hbit) (hcur := hcur))
  have hafter :
      fixedQuadQuadTailAfterReader data i bw b hbit = fixedQuadAfterReader data i bw hbit := by
    exact
      fixedQuadQuadTailAfterReader_eq_fixedQuadAfterReader
        (data := data) (i := i) (bw := bw) (b := b) (hbit := hbit)
        (hbits := hbranch.bitsEq)
  have htail' :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
        (fixedQuadQuadTailStartReader data i bw b hbit)
        (dist1RunOut out b 3) =
        some (fixedQuadAfterReader data i bw hbit,
          fixedQuadOut data (i + 4) (dist1RunOut out b 3)) := by
    simpa [hafter] using htail
  exact
    decodeFixedBlockFuelFast_fixedQuadBitsEob_decode_of_quad_tail
      (data := data) (i := i) (bw := bw) (out := out) (b := b) (hbit := hbit)
      (hbits := hbranch.bitsEq) (hsteps := hbranch.stepsEq) (houtEq := hbranch.outEq)
      (hstep := hstep) (htail := htail')

lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_exact_literal_branch
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (b : UInt8) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    (hbranch : FixedQuadLiteralBranchData data i out b)
    (htail :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
        (fixedQuadLiteralTailStartReader data i bw b hbit)
        (out.push b) =
        some (fixedQuadLiteralTailAfterReader data i bw b hbit,
          fixedQuadOut data (i + 1) (out.push b))) :
    decodeFixedBlockFuelFast (fixedQuadStepsEob data i)
      (fixedQuadStartReader data i bw hbit) out =
      some (fixedQuadAfterReader data i bw hbit, fixedQuadOut data i out) := by
  have htail2 : 2 ≤ fixedQuadLiteralTailLen data i := by
    simpa [fixedQuadLiteralTailLen] using fixedQuadBitsEob_len_ge_two data (i + 1)
  have hstep :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1) + 1)
        (BitWriter.readerAt bw
          (BitWriter.writeBits bw (literalRepeatBitsTail b 1
            (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)).1
            (literalRepeatBitsTail b 1
              (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)).2).flush
          (flush_size_writeBits_le bw
            (literalRepeatBitsTail b 1
              (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)).1
            (literalRepeatBitsTail b 1
              (fixedQuadLiteralTailBits data i) (fixedQuadLiteralTailLen data i)).2) hbit) out =
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
        (fixedQuadLiteralTailStartReader data i bw b hbit) (out.push b) := by
    simpa [fixedQuadLiteralTailStartReader, fixedQuadLiteralTailBits, fixedQuadLiteralTailLen] using
      (decodeFixedBlockFuelFast_step_literal_readerAt_writeBits_tail
      (fuel := fixedQuadStepsEob data (i + 1)) (bw := bw) (b := b)
      (tailBits := fixedQuadLiteralTailBits data i) (tailLen := fixedQuadLiteralTailLen data i)
      (out := out)
      (htail2 := htail2) (hbit := hbit) (hcur := hcur))
  have hafter :
      fixedQuadLiteralTailAfterReader data i bw b hbit = fixedQuadAfterReader data i bw hbit := by
    exact
      fixedQuadLiteralTailAfterReader_eq_fixedQuadAfterReader
        (data := data) (i := i) (bw := bw) (b := b) (hbit := hbit)
        (hbits := hbranch.bitsEq)
  have htail' :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
        (fixedQuadLiteralTailStartReader data i bw b hbit)
        (out.push b) =
        some (fixedQuadAfterReader data i bw hbit,
          fixedQuadOut data (i + 1) (out.push b)) := by
    simpa [hafter] using htail
  exact
    decodeFixedBlockFuelFast_fixedQuadBitsEob_decode_of_literal_tail
      (data := data) (i := i) (bw := bw) (out := out) (b := b) (hbit := hbit)
      (hbits := hbranch.bitsEq) (hsteps := hbranch.stepsEq) (houtEq := hbranch.outEq)
      (hstep := hstep) (htail := htail')

set_option maxHeartbeats 0 in
private lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_quad_tail_adapter
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (b : UInt8) (hbit : bw.bitPos < 8)
    (hrec :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
          (fixedQuadQuadRecursiveStartReader data i bw b hbit)
          (dist1RunOut out b 3) =
        some
          (fixedQuadQuadRecursiveAfterReader data i bw b hbit,
           fixedQuadOut data (i + 4) (dist1RunOut out b 3))) :
    decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
      (fixedQuadQuadTailStartReader data i bw b hbit)
      (dist1RunOut out b 3) =
      some
        (fixedQuadQuadTailAfterReader data i bw b hbit,
         fixedQuadOut data (i + 4) (dist1RunOut out b 3)) := by
  rw [fixedQuadQuadRecursiveStartReader_eq_fixedQuadQuadTailStartReader,
    fixedQuadQuadRecursiveAfterReader_eq_fixedQuadQuadTailAfterReader] at hrec
  exact hrec

set_option maxHeartbeats 0 in
private lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_literal_tail_adapter
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (b : UInt8) (hbit : bw.bitPos < 8)
    (hrec :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
          (fixedQuadLiteralRecursiveStartReader data i bw b hbit)
          (out.push b) =
        some
          (fixedQuadLiteralRecursiveAfterReader data i bw b hbit,
           fixedQuadOut data (i + 1) (out.push b))) :
    decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
      (fixedQuadLiteralTailStartReader data i bw b hbit)
      (out.push b) =
      some
        (fixedQuadLiteralTailAfterReader data i bw b hbit,
         fixedQuadOut data (i + 1) (out.push b)) := by
  rw [fixedQuadLiteralRecursiveStartReader_eq_fixedQuadLiteralTailStartReader,
    fixedQuadLiteralRecursiveAfterReader_eq_fixedQuadLiteralTailAfterReader] at hrec
  exact hrec

private lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_exact_quad_dispatch
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (b : UInt8)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    (hbranch : FixedQuadQuadBranchData data i out b)
    (hrec :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
          (fixedQuadQuadRecursiveStartReader data i bw b hbit)
          (dist1RunOut out b 3) =
        some
          (fixedQuadQuadRecursiveAfterReader data i bw b hbit,
           fixedQuadOut data (i + 4) (dist1RunOut out b 3))) :
    decodeFixedBlockFuelFast (fixedQuadStepsEob data i) (fixedQuadStartReader data i bw hbit) out =
      some (fixedQuadAfterReader data i bw hbit, fixedQuadOut data i out) := by
  have htail :=
    decodeFixedBlockFuelFast_fixedQuadBitsEob_quad_tail_adapter
      (data := data) (i := i) (bw := bw) (out := out) (b := b)
      (hbit := hbit) hrec
  exact
    decodeFixedBlockFuelFast_fixedQuadBitsEob_exact_quad_branch
      (data := data) (i := i) (bw := bw) (out := out) (b := b)
      (hbit := hbit) (hcur := hcur) (hbranch := hbranch)
      (htail := htail)

private lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_exact_literal_dispatch
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (b : UInt8)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    (hbranch : FixedQuadLiteralBranchData data i out b)
    (hrec :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
          (fixedQuadLiteralRecursiveStartReader data i bw b hbit)
          (out.push b) =
        some
          (fixedQuadLiteralRecursiveAfterReader data i bw b hbit,
           fixedQuadOut data (i + 1) (out.push b))) :
    decodeFixedBlockFuelFast (fixedQuadStepsEob data i) (fixedQuadStartReader data i bw hbit) out =
      some (fixedQuadAfterReader data i bw hbit, fixedQuadOut data i out) := by
  have htail :=
    decodeFixedBlockFuelFast_fixedQuadBitsEob_literal_tail_adapter
      (data := data) (i := i) (bw := bw) (out := out) (b := b)
      (hbit := hbit) hrec
  exact
    decodeFixedBlockFuelFast_fixedQuadBitsEob_exact_literal_branch
      (data := data) (i := i) (bw := bw) (out := out) (b := b)
      (hbit := hbit) (hcur := hcur) (hbranch := hbranch)
      (htail := htail)

private lemma fixedQuad_measure_lt_literal (data : Array UInt8) {i : Nat}
    (h : i < data.size) : data.size - (i + 1) < data.size - i := by
  omega

private lemma fixedQuad_measure_lt_quad (data : Array UInt8) {i : Nat}
    (h : i + 3 < data.size) : data.size - (i + 4) < data.size - i := by
  omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exact
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    :
    decodeFixedBlockFuelFast (fixedQuadStepsEob data i) (fixedQuadStartReader data i bw hbit) out =
      some (fixedQuadAfterReader data i bw hbit, fixedQuadOut data i out) := by
  by_cases hlt : i < data.size
  · let b := data[i]
    have hb : b = data[i]'hlt := rfl
    by_cases h3 : i + 3 < data.size
    · by_cases hq : quadTailEqb data i b h3 = true
      · have hbranch :=
          fixedQuadBranchData_of_quad
            (data := data) (i := i) (out := out) (b := b)
            (h := hlt) (h3 := h3) (hb := hb) (hq := hq)
        have hrecQuad :
            decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
              (fixedQuadQuadRecursiveStartReader data i bw b hbit)
              (dist1RunOut out b 3) =
              some
                (fixedQuadQuadRecursiveAfterReader data i bw b hbit,
                 fixedQuadOut data (i + 4) (dist1RunOut out b 3)) := by
          simpa [fixedQuadQuadRecursiveStartReader, fixedQuadQuadRecursiveAfterReader,
            fixedQuadQuadRecursiveBitPosLt, fixedQuadStartReader, fixedQuadAfterReader] using
            (decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exact
            (data := data) (i := i + 4)
            (bw := fixedQuadQuadTailWriter data i bw b)
            (out := dist1RunOut out b 3)
            (hbit := fixedQuadQuadRecursiveBitPosLt data i bw b hbit)
            (hcur := fixedQuadQuadRecursiveCurClearAbove data i bw b hbit hcur))
        exact
          decodeFixedBlockFuelFast_fixedQuadBitsEob_exact_quad_dispatch
            (data := data) (i := i) (bw := bw) (out := out) (b := b)
            (hbit := hbit) (hcur := hcur)
            (hbranch := hbranch)
            (hrec := hrecQuad)
      · have hqFalse : quadTailEqb data i b h3 = false := by
          cases hqb : quadTailEqb data i b h3 <;> simp_all
        have hbranch := fixedQuadBranchData_of_lit_hqFalse
          (data := data) (i := i) (out := out) (b := b)
          (h := hlt) (h3 := h3) (hb := hb) (hq := hqFalse)
        have hrecLiteral :
            decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
              (fixedQuadLiteralRecursiveStartReader data i bw b hbit)
              (out.push b) =
              some
                (fixedQuadLiteralRecursiveAfterReader data i bw b hbit,
                 fixedQuadOut data (i + 1) (out.push b)) := by
          simpa [fixedQuadLiteralRecursiveStartReader, fixedQuadLiteralRecursiveAfterReader,
            fixedQuadLiteralRecursiveBitPosLt, fixedQuadStartReader, fixedQuadAfterReader] using
            (decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exact
            (data := data) (i := i + 1)
            (bw := fixedQuadLiteralTailWriter data i bw b)
            (out := out.push b)
            (hbit := fixedQuadLiteralRecursiveBitPosLt data i bw b hbit)
            (hcur := fixedQuadLiteralRecursiveCurClearAbove data i bw b hbit hcur))
        exact
          decodeFixedBlockFuelFast_fixedQuadBitsEob_exact_literal_dispatch
            (data := data) (i := i) (bw := bw) (out := out) (b := b)
            (hbit := hbit) (hcur := hcur)
            (hbranch := hbranch)
            (hrec := hrecLiteral)
    · have hbranch := fixedQuadBranchData_of_lit_noh3
        (data := data) (i := i) (out := out) (b := b)
        (h := hlt) (h3 := h3) (hb := hb)
      have hrecLiteral :
          decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
            (fixedQuadLiteralRecursiveStartReader data i bw b hbit)
            (out.push b) =
            some
              (fixedQuadLiteralRecursiveAfterReader data i bw b hbit,
               fixedQuadOut data (i + 1) (out.push b)) := by
        simpa [fixedQuadLiteralRecursiveStartReader, fixedQuadLiteralRecursiveAfterReader,
          fixedQuadLiteralRecursiveBitPosLt, fixedQuadStartReader, fixedQuadAfterReader] using
          (decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exact
          (data := data) (i := i + 1)
          (bw := fixedQuadLiteralTailWriter data i bw b)
          (out := out.push b)
          (hbit := fixedQuadLiteralRecursiveBitPosLt data i bw b hbit)
          (hcur := fixedQuadLiteralRecursiveCurClearAbove data i bw b hbit hcur))
      exact
        decodeFixedBlockFuelFast_fixedQuadBitsEob_exact_literal_dispatch
          (data := data) (i := i) (bw := bw) (out := out) (b := b)
          (hbit := hbit) (hcur := hcur)
          (hbranch := hbranch)
          (hrec := hrecLiteral)
  · have hbase :
        decodeFixedBlockFuelFast (fixedQuadStepsEob data i) (fixedQuadStartReader data i bw hbit) out =
          some (eobNoTailAfterReader bw hbit, fixedQuadOut data i out) := by
      have hbase0 := decodeFixedBlockFuelFast_step_eob_eobNoTail
        (fuel := 0) (bw := bw) (out := out) (hbit := hbit) (hcur := hcur)
      simpa [fixedQuadStartReader, fixedQuadBitsEob_unfold, fixedQuadStepsEob_unfold, fixedQuadOut_unfold, hlt,
        eobNoTailWriter, eobNoTailStartReader, eobNoTailAfterReader] using hbase0
    have hfinal :
        eobNoTailAfterReader bw hbit = fixedQuadAfterReader data i bw hbit := by
      simpa [fixedQuadAfterReader, fixedQuadBitsEob_unfold, hlt, eobNoTailWriter, eobNoTailAfterReader, flushReader]
    simpa [hfinal] using hbase
termination_by data.size - i
decreasing_by
  all_goals
    first
      | exact fixedQuad_measure_lt_quad data h3
      | exact fixedQuad_measure_lt_literal data hlt

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_reader_eq
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    (brAfter : BitReader)
    (hdecode :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data i)
        (fixedQuadStartReader data i bw hbit) out =
        some (brAfter, fixedQuadOut data i out)) :
    brAfter = fixedQuadAfterReader data i bw hbit := by
  have hexact :=
    decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exact
      (data := data) (i := i) (bw := bw) (out := out) (hbit := hbit) (hcur := hcur)
  have hpair :
      (brAfter, fixedQuadOut data i out) =
        (fixedQuadAfterReader data i bw hbit, fixedQuadOut data i out) := by
    exact Option.some.inj (hdecode.symm.trans hexact)
  simpa using congrArg Prod.fst hpair

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exists
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    ∃ brAfter,
      decodeFixedBlockFuelFast (fixedQuadStepsEob data i)
        (fixedQuadStartReader data i bw hbit) out =
        some (brAfter, fixedQuadOut data i out) := by
  refine ⟨fixedQuadAfterReader data i bw hbit, ?_⟩
  exact
    decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exact
      (data := data) (i := i) (bw := bw) (out := out) (hbit := hbit) (hcur := hcur)

set_option maxRecDepth 200000 in

-- Static Huffman length base table size.
lemma lengthBases_size : lengthBases.size = 29 := by decide
-- Static Huffman length extra table size.
lemma lengthExtra_size : lengthExtra.size = 29 := by decide
-- Static Huffman distance base table size.
lemma distBases_size : distBases.size = 30 := by decide
-- Static Huffman distance extra table size.
lemma distExtra_size : distExtra.size = 30 := by decide

end Png
end Bitmaps
