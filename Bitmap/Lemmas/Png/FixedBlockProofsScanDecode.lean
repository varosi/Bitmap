import Bitmap.Lemmas.Png.FixedBlockProofsDecode
import Bitmap.Lemmas.Png.FixedBlockProofsScanBase

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

lemma chooseFixedMatchChunkLen_three : chooseFixedMatchChunkLen 3 = 3 := by
  simp [chooseFixedMatchChunkLen]

lemma dist1ChunkLoopSteps_three : dist1ChunkLoopSteps 3 = 1 := by
  have h3 : 3 ≤ 3 := by decide
  have hstep := dist1ChunkLoopSteps_of_ge3 3 h3
  have hrem : 3 - chooseFixedMatchChunkLen 3 = 0 := by
    simp [chooseFixedMatchChunkLen_three]
  have h0 : dist1ChunkLoopSteps 0 = 0 := by
    exact dist1ChunkLoopSteps_of_lt3 0 (by decide)
  calc
    dist1ChunkLoopSteps 3 = 1 + dist1ChunkLoopSteps (3 - chooseFixedMatchChunkLen 3) := hstep
    _ = 1 + dist1ChunkLoopSteps 0 := by simp [hrem]
    _ = 1 := by simp [h0]

lemma dist1ChunkLoopRem_three : dist1ChunkLoopRem 3 = 0 := by
  have h3 : 3 ≤ 3 := by decide
  have hstep := dist1ChunkLoopRem_of_ge3 3 h3
  have hrem : 3 - chooseFixedMatchChunkLen 3 = 0 := by
    simp [chooseFixedMatchChunkLen_three]
  have h0 : dist1ChunkLoopRem 0 = 0 := by
    exact dist1ChunkLoopRem_of_lt3 0 (by decide)
  calc
    dist1ChunkLoopRem 3 = dist1ChunkLoopRem (3 - chooseFixedMatchChunkLen 3) := hstep
    _ = dist1ChunkLoopRem 0 := by simp [hrem]
    _ = 0 := h0

lemma dist1RunSteps_three : dist1RunSteps 3 = 2 := by
  simp [dist1RunSteps, dist1ChunkLoopSteps_three, dist1ChunkLoopRem_three]

@[simp] lemma fixedLenMatchInfo_three : fixedLenMatchInfo 3 = (257, 0, 0) := by
  simp [fixedLenMatchInfo]

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

def literalThenMatch3Dist1StartReader (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bitsLen := dist1RunBitsTail b 3 tailBits tailLen
  BitWriter.readerAt bw (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
    (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit

@[simp] lemma dist1RunBitsTail_three (b : UInt8) (tailBits tailLen : Nat) :
    dist1RunBitsTail b 3 tailBits tailLen =
      let chunkBits := dist1ChunkLoopBitsTail 3 tailBits tailLen
      let codeLen := fixedLitLenCode b.toNat
      let bits := reverseBits codeLen.1 codeLen.2
      let bitsTot := bits ||| (chunkBits.1 <<< codeLen.2)
      let lenTot := codeLen.2 + chunkBits.2
      (bitsTot, lenTot) := by
  simp [dist1RunBitsTail, dist1ChunkLoopRem_three, literalRepeatBitsTail_zero]

@[simp] lemma dist1ChunkLoopBitsTail_three (tailBits tailLen : Nat) :
    dist1ChunkLoopBitsTail 3 tailBits tailLen =
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
      (bitsTot, lenTot) := by
  have h3 : 3 ≤ 3 := by decide
  have hge := dist1ChunkLoopBitsTail_of_ge3 3 tailBits tailLen h3
  have h0 : dist1ChunkLoopBitsTail 0 tailBits tailLen = (tailBits, tailLen) := by
    exact dist1ChunkLoopBitsTail_of_lt3 0 tailBits tailLen (by decide)
  simpa [chooseFixedMatchChunkLen_three, h0] using hge

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
  let chunkBits := dist1ChunkLoopBitsTail 3 tailBits tailLen
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (chunkBits.1 <<< codeLen.2)
  let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
  match3Dist1AfterReader bw1 tailBits tailLen (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit)

def literalThenMatch3Dist1TailWriter (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) : BitWriter :=
  let chunkBits := dist1ChunkLoopBitsTail 3 tailBits tailLen
  let codeLenLit := fixedLitLenCode b.toNat
  let bitsLit := reverseBits codeLenLit.1 codeLenLit.2
  let bitsTotLit := bitsLit ||| (chunkBits.1 <<< codeLenLit.2)
  let bw1 := BitWriter.writeBits bw bitsTotLit codeLenLit.2
  let info := fixedLenMatchInfo 3
  let sym := info.1
  let extraBits := info.2.1
  let extraLen := info.2.2
  let codeLen := fixedLitLenCode sym
  let symBits := reverseBits codeLen.1 codeLen.2
  let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
  let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
  let bwM1 := BitWriter.writeBits bw1 (symBits ||| (lenBitsTot <<< codeLen.2)) codeLen.2
  let bwM2 := BitWriter.writeBits bwM1 lenBitsTot extraLen
  BitWriter.writeBits bwM2 distBitsTot 5

lemma literalThenMatch3Dist1TailWriter_bitPos_lt
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (hbit : bw.bitPos < 8) :
    (literalThenMatch3Dist1TailWriter bw b tailBits tailLen).bitPos < 8 := by
  dsimp [literalThenMatch3Dist1TailWriter]
  repeat
    first | apply bitPos_lt_8_writeBits
  exact hbit

lemma literalThenMatch3Dist1TailWriter_curClearAbove
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (literalThenMatch3Dist1TailWriter bw b tailBits tailLen).curClearAbove := by
  dsimp [literalThenMatch3Dist1TailWriter]
  repeat
    first | apply curClearAbove_writeBits | apply bitPos_lt_8_writeBits | assumption

def literalThenMatch3Dist1TailStartReader (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bwTail := literalThenMatch3Dist1TailWriter bw b tailBits tailLen
  BitWriter.readerAt bwTail (BitWriter.writeBits bwTail tailBits tailLen).flush
    (flush_size_writeBits_le bwTail tailBits tailLen)
    (literalThenMatch3Dist1TailWriter_bitPos_lt bw b tailBits tailLen hbit)

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
  let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
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
  have hbit1 : bw1.bitPos < 8 := by
    exact bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit
  have hcur1 : bw1.curClearAbove := by
    exact curClearAbove_writeBits bw bitsTot codeLen.2 hbit hcur
  have hMatch :=
    decodeFixedBlockFuelFast_match3Dist1_readerAt_writeBits
      (fuel := fuel) (bw := bw1) (tailBits := tailBits) (tailLen := tailLen)
      (out := out.push b) (hout := by simp [ByteArray.size_push]) (hbit := hbit1) (hcur := hcur1)
  have hbwAll' :
      bwAll = BitWriter.writeBits bw1 chunkBits.1 chunkBits.2 := by
    dsimp [bwAll, bw1]
    simpa [hwriteBits] using hconcat
  have hMidChunk :
      brMid =
        BitWriter.readerAt bw1 (BitWriter.writeBits bw1 chunkBits.1 chunkBits.2).flush
          (flush_size_writeBits_le bw1 chunkBits.1 chunkBits.2) hbit1 := by
    apply BitReader.ext
    · change (BitWriter.writeBits bw bitsTot lenTot).flush =
          (BitWriter.writeBits bw1 chunkBits.1 chunkBits.2).flush
      simpa [bwAll] using congrArg BitWriter.flush hbwAll'
    · change (BitWriter.writeBits bw bitsTot codeLen.2).out.size = bw1.out.size
      simpa [bw1] using congrArg BitWriter.out hwriteBits
    · change (BitWriter.writeBits bw bitsTot codeLen.2).bitPos = bw1.bitPos
      simpa [bw1] using congrArg BitWriter.bitPos hwriteBits
  have hMatchStartEq :
      match3Dist1StartReader bw1 tailBits tailLen hbit1 =
        BitWriter.readerAt bw1 (BitWriter.writeBits bw1 chunkBits.1 chunkBits.2).flush
          (flush_size_writeBits_le bw1 chunkBits.1 chunkBits.2) hbit1 := by
    simp [match3Dist1StartReader, chunkBits]
  have hMidEq :
      brMid = match3Dist1StartReader bw1 tailBits tailLen hbit1 := by
    exact hMidChunk.trans hMatchStartEq.symm
  have hlast : (out.push b).get! ((out.push b).size - 1) = b := by
    simpa using get!_last_push out b
  have hpush :
      pushRepeat (out.push b) ((out.push b).get! ((out.push b).size - 1)) 3 = dist1RunOut out b 3 := by
    calc
      pushRepeat (out.push b) ((out.push b).get! ((out.push b).size - 1)) 3
          = pushRepeat (out.push b) b 3 := by
              exact congrArg (fun x => pushRepeat (out.push b) x 3) hlast
      _ = dist1RunOut out b 3 := by rfl
  have hAfter :
      literalThenMatch3Dist1AfterReader bw b tailBits tailLen hbit =
        match3Dist1AfterReader bw1 tailBits tailLen hbit1 := by
    simpa [literalThenMatch3Dist1AfterReader, bw1, chunkBits, codeLen, bits, bitsTot]
  have hMatchStep :
      decodeFixedBlockFuelFast (fuel + 1) brMid (out.push b) =
        decodeFixedBlockFuelFast fuel (literalThenMatch3Dist1AfterReader bw b tailBits tailLen hbit)
          (dist1RunOut out b 3) := by
    rw [hMidEq, hAfter]
    have hMatchB :
        decodeFixedBlockFuelFast (fuel + 1) (match3Dist1StartReader bw1 tailBits tailLen hbit1) (out.push b) =
          decodeFixedBlockFuelFast fuel (match3Dist1AfterReader bw1 tailBits tailLen hbit1)
            (pushRepeat (out.push b) b 3) := by
      simpa only [hlast] using hMatch
    simpa [dist1RunOut] using hMatchB
  exact hLitStep.trans (by simpa [brMid] using hMatchStep)

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
  let chunkBits := dist1ChunkLoopBitsTail 3 tailBits tailLen
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (chunkBits.1 <<< codeLen.2)
  let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
  have hbit1 : bw1.bitPos < 8 := by
    dsimp [bw1]
    exact bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit
  have hafterMatch :
      literalThenMatch3Dist1AfterReader bw b tailBits tailLen hbit =
        match3Dist1AfterReader bw1 tailBits tailLen hbit1 := by
    simpa [literalThenMatch3Dist1AfterReader, bw1, chunkBits, codeLen, bits, bitsTot]
  have hafterTail :
      literalThenMatch3Dist1AfterReader bw b tailBits tailLen hbit =
        literalThenMatch3Dist1TailStartReader bw b tailBits tailLen hbit := by
    calc
      literalThenMatch3Dist1AfterReader bw b tailBits tailLen hbit
          = match3Dist1AfterReader bw1 tailBits tailLen hbit1 := hafterMatch
      _ = match3Dist1TailStartReader bw1 tailBits tailLen hbit1 := by
            exact match3Dist1AfterReader_eq_tailStartReader (bw := bw1)
              (tailBits := tailBits) (tailLen := tailLen) (hbit := hbit1)
      _ = literalThenMatch3Dist1TailStartReader bw b tailBits tailLen hbit := by
            rfl
  simpa [hafterTail] using hmain

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exists
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    ∃ brAfter,
      decodeFixedBlockFuelFast (fixedQuadStepsEob data i)
        (BitWriter.readerAt bw
          (BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2).flush
          (flush_size_writeBits_le bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2) hbit) out =
        some (brAfter, fixedQuadOut data i out) := by
  classical
  by_cases hlt : i < data.size
  · let b := data[i]
    by_cases h3 : i + 3 < data.size
    · by_cases hq : quadTailEqb data i b h3 = true
      · let tailBits := (fixedQuadBitsEob data (i + 4)).1
        let tailLen := (fixedQuadBitsEob data (i + 4)).2
        have htail2 : 2 ≤ tailLen := by
          dsimp [tailLen]
          exact fixedQuadBitsEob_len_ge_two data (i + 4)
        have hstep :=
          decodeFixedBlockFuelFast_literalThenMatch3Dist1_readerAt_writeBits_tail
            (fuel := fixedQuadStepsEob data (i + 4)) (bw := bw) (b := b)
            (tailBits := tailBits) (tailLen := tailLen) (out := out)
            (htail2 := htail2) (hbit := hbit) (hcur := hcur)
        have hbitTail :
            (literalThenMatch3Dist1TailWriter bw b tailBits tailLen).bitPos < 8 := by
          exact literalThenMatch3Dist1TailWriter_bitPos_lt bw b tailBits tailLen hbit
        have hcurTail :
            (literalThenMatch3Dist1TailWriter bw b tailBits tailLen).curClearAbove := by
          exact literalThenMatch3Dist1TailWriter_curClearAbove bw b tailBits tailLen hbit hcur
        rcases
          (decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exists
            (data := data) (i := i + 4)
            (bw := literalThenMatch3Dist1TailWriter bw b tailBits tailLen)
            (out := dist1RunOut out b 3) (hbit := hbitTail) (hcur := hcurTail))
          with ⟨brAfter, hih⟩
        have hih' :
            decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 4))
              (literalThenMatch3Dist1TailStartReader bw b tailBits tailLen hbit)
              (dist1RunOut out b 3) =
              some (brAfter, fixedQuadOut data (i + 4) (dist1RunOut out b 3)) := by
          simpa [tailBits, tailLen, b] using hih
        refine ⟨brAfter, ?_⟩
        have hbits :
            fixedQuadBitsEob data i = dist1RunBitsTail b 3 tailBits tailLen := by
          simpa [b, tailBits, tailLen] using
            (fixedQuadBitsEob_of_quad (data := data) (i := i) (h := hlt) (h3 := h3)
              (hq := by simpa [b] using hq))
        have hsteps :
            fixedQuadStepsEob data i = 2 + fixedQuadStepsEob data (i + 4) := by
          have hsteps0 :=
            fixedQuadStepsEob_of_quad (data := data) (i := i) (h := hlt) (h3 := h3)
              (hq := by simpa [b] using hq)
          simpa [dist1RunSteps_three, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsteps0
        have houtEq :
            fixedQuadOut data i out = fixedQuadOut data (i + 4) (dist1RunOut out b 3) := by
          simpa [b] using
            (fixedQuadOut_of_quad (data := data) (i := i) (out := out) (h := hlt) (h3 := h3)
              (hq := by simpa [b] using hq))
        have hstart :
            (BitWriter.readerAt bw
              (BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2).flush
              (flush_size_writeBits_le bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2) hbit) =
              literalThenMatch3Dist1StartReader bw b tailBits tailLen hbit := by
          dsimp [literalThenMatch3Dist1StartReader]
          simp [hbits, dist1RunBitsTail_three]
        exact (by
          simpa [b, tailBits, tailLen, hstart, hbits, hsteps, houtEq,
            literalThenMatch3Dist1StartReader, dist1RunBitsTail_three,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep.trans hih')
      · let tailBits := (fixedQuadBitsEob data (i + 1)).1
        let tailLen := (fixedQuadBitsEob data (i + 1)).2
        have htail2 : 2 ≤ tailLen := by
          dsimp [tailLen]
          exact fixedQuadBitsEob_len_ge_two data (i + 1)
        have hstep :=
          decodeFixedBlockFuelFast_step_literal_readerAt_writeBits_tail
            (fuel := fixedQuadStepsEob data (i + 1)) (bw := bw) (b := b)
            (tailBits := tailBits) (tailLen := tailLen) (out := out)
            (htail2 := htail2) (hbit := hbit) (hcur := hcur)
        have hbitTail : (literalTailWriter bw b tailBits tailLen).bitPos < 8 := by
          exact literalTailWriter_bitPos_lt bw b tailBits tailLen hbit
        have hcurTail : (literalTailWriter bw b tailBits tailLen).curClearAbove := by
          exact literalTailWriter_curClearAbove bw b tailBits tailLen hbit hcur
        rcases
          (decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exists
            (data := data) (i := i + 1) (bw := literalTailWriter bw b tailBits tailLen)
            (out := out.push b) (hbit := hbitTail) (hcur := hcurTail))
          with ⟨brAfter, hih⟩
        have hih' :
            decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
              (literalTailStartReader bw b tailBits tailLen hbit) (out.push b) =
              some (brAfter, fixedQuadOut data (i + 1) (out.push b)) := by
          simpa [tailBits, tailLen, b] using hih
        refine ⟨brAfter, ?_⟩
        have hbits :
            fixedQuadBitsEob data i =
              literalRepeatBitsTail b 1 tailBits tailLen := by
          simpa [b, tailBits, tailLen] using
            (fixedQuadBitsEob_of_lit_hqFalse (data := data) (i := i) (h := hlt) (h3 := h3)
              (hq := by simpa [b] using hq))
        have hsteps :
            fixedQuadStepsEob data i = 1 + fixedQuadStepsEob data (i + 1) := by
          simpa [b] using
            (fixedQuadStepsEob_of_lit_hqFalse (data := data) (i := i) (h := hlt) (h3 := h3)
              (hq := by simpa [b] using hq))
        have houtEq :
            fixedQuadOut data i out = fixedQuadOut data (i + 1) (out.push b) := by
          simpa [b] using
            (fixedQuadOut_of_lit_hqFalse (data := data) (i := i) (out := out) (h := hlt) (h3 := h3)
              (hq := by simpa [b] using hq))
        exact (by
          simpa [b, tailBits, tailLen, hbits, hsteps, houtEq,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep.trans hih')
    · let tailBits := (fixedQuadBitsEob data (i + 1)).1
      let tailLen := (fixedQuadBitsEob data (i + 1)).2
      have htail2 : 2 ≤ tailLen := by
        dsimp [tailLen]
        exact fixedQuadBitsEob_len_ge_two data (i + 1)
      have hstep :=
        decodeFixedBlockFuelFast_step_literal_readerAt_writeBits_tail
          (fuel := fixedQuadStepsEob data (i + 1)) (bw := bw) (b := b)
          (tailBits := tailBits) (tailLen := tailLen) (out := out)
          (htail2 := htail2) (hbit := hbit) (hcur := hcur)
      have hbitTail : (literalTailWriter bw b tailBits tailLen).bitPos < 8 := by
        exact literalTailWriter_bitPos_lt bw b tailBits tailLen hbit
      have hcurTail : (literalTailWriter bw b tailBits tailLen).curClearAbove := by
        exact literalTailWriter_curClearAbove bw b tailBits tailLen hbit hcur
      rcases
        (decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exists
          (data := data) (i := i + 1) (bw := literalTailWriter bw b tailBits tailLen)
          (out := out.push b) (hbit := hbitTail) (hcur := hcurTail))
        with ⟨brAfter, hih⟩
      have hih' :
          decodeFixedBlockFuelFast (fixedQuadStepsEob data (i + 1))
            (literalTailStartReader bw b tailBits tailLen hbit) (out.push b) =
            some (brAfter, fixedQuadOut data (i + 1) (out.push b)) := by
        simpa [tailBits, tailLen, b] using hih
      refine ⟨brAfter, ?_⟩
      have hbits :
          fixedQuadBitsEob data i =
            literalRepeatBitsTail b 1 tailBits tailLen := by
        simpa [b, tailBits, tailLen] using
          (fixedQuadBitsEob_of_lit_noh3 (data := data) (i := i) (h := hlt) (h3 := h3))
      have hsteps :
          fixedQuadStepsEob data i = 1 + fixedQuadStepsEob data (i + 1) := by
        simpa [b] using
          (fixedQuadStepsEob_of_lit_noh3 (data := data) (i := i) (h := hlt) (h3 := h3))
      have houtEq :
          fixedQuadOut data i out = fixedQuadOut data (i + 1) (out.push b) := by
        simpa [b] using
          (fixedQuadOut_of_lit_noh3 (data := data) (i := i) (out := out) (h := hlt) (h3 := h3))
      exact (by
        simpa [b, tailBits, tailLen, hbits, hsteps, houtEq,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep.trans hih')
  · refine ⟨eobNoTailAfterReader bw hbit, ?_⟩
    have hbase := decodeFixedBlockFuelFast_step_eob_eobNoTail
      (fuel := 0) (bw := bw) (out := out) (hbit := hbit) (hcur := hcur)
    simpa [fixedQuadBitsEob_unfold, fixedQuadStepsEob_unfold, fixedQuadOut_unfold, hlt,
      eobNoTailWriter, eobNoTailStartReader, eobNoTailAfterReader]
      using hbase
termination_by data.size - i
decreasing_by
  all_goals omega

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
