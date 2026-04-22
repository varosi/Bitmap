import Bitmap.Lemmas.Png.FixedBlockBase
import Bitmap.Lemmas.Png.FixedBlockProofsCommon
import Bitmap.Lemmas.Png.FixedBlockProofsDecode
import Bitmap.Lemmas.Png.FixedBlockProofsScanBase

namespace Bitmaps

namespace Lemmas

open Png
attribute [local simp] Png.byteArray_get_proof_irrel

set_option maxRecDepth 200000 in
lemma sameByteRunEndFast_eq_sameByteRunEnd
    (data : Array UInt8) (b : UInt8) (j : Nat) :
    sameByteRunEndFast data b j = sameByteRunEnd data b j := by
  have hk :
      ∀ k, ∀ j0, data.size - j0 = k →
        sameByteRunEndFast data b j0 = sameByteRunEnd data b j0 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro j0 hk
        rw [sameByteRunEndFast.eq_def, sameByteRunEnd.eq_def]
        by_cases h : j0 < data.size
        · by_cases heq : data[j0]'h = b
          · simp [h, heq]
            have hk' : data.size - (j0 + 1) < k := by
              have hlt' : data.size - (j0 + 1) < data.size - j0 := by
                exact Nat.sub_lt_sub_left (k := j0) (m := data.size) (n := j0 + 1) h
                  (Nat.lt_succ_self j0)
              simpa [hk] using hlt'
            exact ih (data.size - (j0 + 1)) hk' (j0 + 1) rfl
          · simp [h, heq]
        · simp [h]
  exact hk (data.size - j) j rfl

lemma literalRepeatTailWriter_eq_writeFixedLiteralRepeatFast
    (bw : BitWriter) (b : UInt8) (n tailBits tailLen : Nat) :
    literalRepeatTailWriter bw b n tailBits tailLen = bw.writeFixedLiteralRepeatFast b n := by
  induction n generalizing bw with
  | zero =>
      simp [literalRepeatTailWriter, BitWriter.writeFixedLiteralRepeatFast]
  | succ n ih =>
      dsimp [literalRepeatTailWriter, BitWriter.writeFixedLiteralRepeatFast]
      rw [literalTailWriter_eq_writeFixedLiteralFast]
      simpa using ih (bw := BitWriter.writeFixedLiteralFast bw b)

lemma writeFixedLiteralFast_bitPos_lt
    (bw : BitWriter) (b : UInt8) (hbit : bw.bitPos < 8) :
    (BitWriter.writeFixedLiteralFast bw b).bitPos < 8 := by
  have hbit' := literalTailWriter_bitPos_lt bw b 0 0 hbit
  rw [literalTailWriter_eq_writeFixedLiteralFast (bw := bw) (b := b)
    (tailBits := 0) (tailLen := 0)] at hbit'
  exact hbit'

lemma writeFixedLiteralFast_curClearAbove
    (bw : BitWriter) (b : UInt8) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (BitWriter.writeFixedLiteralFast bw b).curClearAbove := by
  have hcur' := literalTailWriter_curClearAbove bw b 0 0 hbit hcur
  rw [literalTailWriter_eq_writeFixedLiteralFast (bw := bw) (b := b)
    (tailBits := 0) (tailLen := 0)] at hcur'
  exact hcur'

lemma literalTailStartReader_eq_runtimeStartReader
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (hbit : bw.bitPos < 8) :
    literalTailStartReader bw b tailBits tailLen hbit =
      BitWriter.readerAt (BitWriter.writeFixedLiteralFast bw b)
        (BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen).flush
        (flush_size_writeBits_le (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen)
        (writeFixedLiteralFast_bitPos_lt bw b hbit) := by
  have hwriter :
      literalTailWriter bw b tailBits tailLen = BitWriter.writeFixedLiteralFast bw b :=
    literalTailWriter_eq_writeFixedLiteralFast bw b tailBits tailLen
  apply BitReader.ext
  · exact congrArg (fun bwTail => (BitWriter.writeBits bwTail tailBits tailLen).flush) hwriter
  · simpa using congrArg (fun bwTail => bwTail.out.size) hwriter
  · simpa using congrArg BitWriter.bitPos hwriter

lemma writeFixedLiteralRepeatFast_bitPos_lt
    (bw : BitWriter) (b : UInt8) (n : Nat) (hbit : bw.bitPos < 8) :
    (bw.writeFixedLiteralRepeatFast b n).bitPos < 8 := by
  have hbit' := literalRepeatTailWriter_bitPos_lt bw b n 0 0 hbit
  rw [literalRepeatTailWriter_eq_writeFixedLiteralRepeatFast (bw := bw) (b := b)
    (n := n) (tailBits := 0) (tailLen := 0)] at hbit'
  exact hbit'

lemma writeFixedLiteralRepeatFast_curClearAbove
    (bw : BitWriter) (b : UInt8) (n : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (bw.writeFixedLiteralRepeatFast b n).curClearAbove := by
  have hcur' := literalRepeatTailWriter_curClearAbove bw b n 0 0 hbit hcur
  rw [literalRepeatTailWriter_eq_writeFixedLiteralRepeatFast (bw := bw) (b := b)
    (n := n) (tailBits := 0) (tailLen := 0)] at hcur'
  exact hcur'

lemma writeFixedMatchDist1ChunksFast_bitPos_lt
    (bw : BitWriter) (remaining : Nat) (hbit : bw.bitPos < 8) :
    (bw.writeFixedMatchDist1ChunksFast remaining).bitPos < 8 := by
  have hwrite :=
    writeBits_dist1ChunkLoopBitsTail
      (bw := bw) (remaining := remaining) (tailBits := 0) (tailLen := 0)
  have hEq :
      BitWriter.writeBits bw (dist1ChunkLoopBitsTail remaining 0 0).1
        (dist1ChunkLoopBitsTail remaining 0 0).2 =
        bw.writeFixedMatchDist1ChunksFast remaining := by
    exact hwrite.trans (by simp [writeBits_zero])
  have hbit' :
      (BitWriter.writeBits bw (dist1ChunkLoopBitsTail remaining 0 0).1
        (dist1ChunkLoopBitsTail remaining 0 0).2).bitPos < 8 := by
    exact bitPos_lt_8_writeBits bw (dist1ChunkLoopBitsTail remaining 0 0).1
      (dist1ChunkLoopBitsTail remaining 0 0).2 hbit
  rw [hEq] at hbit'
  exact hbit'

lemma writeFixedMatchDist1ChunksFast_curClearAbove
    (bw : BitWriter) (remaining : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (bw.writeFixedMatchDist1ChunksFast remaining).curClearAbove := by
  have hwrite :=
    writeBits_dist1ChunkLoopBitsTail
      (bw := bw) (remaining := remaining) (tailBits := 0) (tailLen := 0)
  have hEq :
      BitWriter.writeBits bw (dist1ChunkLoopBitsTail remaining 0 0).1
        (dist1ChunkLoopBitsTail remaining 0 0).2 =
        bw.writeFixedMatchDist1ChunksFast remaining := by
    exact hwrite.trans (by simp [writeBits_zero])
  have hcur' :
      (BitWriter.writeBits bw (dist1ChunkLoopBitsTail remaining 0 0).1
        (dist1ChunkLoopBitsTail remaining 0 0).2).curClearAbove := by
    exact curClearAbove_writeBits bw (dist1ChunkLoopBitsTail remaining 0 0).1
      (dist1ChunkLoopBitsTail remaining 0 0).2 hbit hcur
  rw [hEq] at hcur'
  exact hcur'

lemma literalRepeatTailStartReader_eq_runtimeStartReader
    (bw : BitWriter) (b : UInt8) (n tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) :
    literalRepeatTailStartReader bw b n tailBits tailLen hbit =
      BitWriter.readerAt (bw.writeFixedLiteralRepeatFast b n)
        (BitWriter.writeBits (bw.writeFixedLiteralRepeatFast b n) tailBits tailLen).flush
        (flush_size_writeBits_le (bw.writeFixedLiteralRepeatFast b n) tailBits tailLen)
        (writeFixedLiteralRepeatFast_bitPos_lt bw b n hbit) := by
  apply BitReader.ext
  · change (BitWriter.writeBits (literalRepeatTailWriter bw b n tailBits tailLen) tailBits tailLen).flush =
        (BitWriter.writeBits (bw.writeFixedLiteralRepeatFast b n) tailBits tailLen).flush
    rw [literalRepeatTailWriter_eq_writeFixedLiteralRepeatFast]
  · change (literalRepeatTailWriter bw b n tailBits tailLen).out.size =
        (bw.writeFixedLiteralRepeatFast b n).out.size
    rw [literalRepeatTailWriter_eq_writeFixedLiteralRepeatFast]
  · change (literalRepeatTailWriter bw b n tailBits tailLen).bitPos =
        (bw.writeFixedLiteralRepeatFast b n).bitPos
    rw [literalRepeatTailWriter_eq_writeFixedLiteralRepeatFast]

private lemma readerAt_writeBits_eq_of_writer_eq
    {bw1 bw2 : BitWriter} (h : bw1 = bw2)
    (tailBits tailLen : Nat)
    (hbit1 : bw1.bitPos < 8) (hbit2 : bw2.bitPos < 8) :
    BitWriter.readerAt bw1
      (BitWriter.writeBits bw1 tailBits tailLen).flush
      (flush_size_writeBits_le bw1 tailBits tailLen) hbit1 =
    BitWriter.readerAt bw2
      (BitWriter.writeBits bw2 tailBits tailLen).flush
      (flush_size_writeBits_le bw2 tailBits tailLen) hbit2 := by
  subst h
  apply BitReader.ext <;> simp [BitWriter.readerAt]

private lemma flushReader_eq_of_writer_eq
    {bw1 bw2 : BitWriter} (h : bw1 = bw2)
    (hbit1 : bw1.bitPos < 8) (hbit2 : bw2.bitPos < 8) :
    flushReader bw1 hbit1 = flushReader bw2 hbit2 := by
  subst h
  apply BitReader.ext <;> simp [flushReader, BitWriter.readerAt]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma dist1ChunkLoopTailLitsTailStartReader_eq_runtimeStartReader
    (bw : BitWriter) (remaining : Nat) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) (hrem : 3 ≤ remaining) :
    dist1ChunkLoopTailLitsTailStartReader bw remaining b tailBits tailLen hbit =
      BitWriter.readerAt (bw.writeFixedMatchDist1ChunksFast remaining)
        (BitWriter.writeBits (bw.writeFixedMatchDist1ChunksFast remaining) tailBits tailLen).flush
        (flush_size_writeBits_le (bw.writeFixedMatchDist1ChunksFast remaining) tailBits tailLen)
        (writeFixedMatchDist1ChunksFast_bitPos_lt bw remaining hbit) := by
  revert bw b tailBits tailLen hbit hrem
  refine Nat.strong_induction_on remaining ?_
  intro remaining ih bw b tailBits tailLen hbit hrem
  have hreaderGe :=
    dist1ChunkLoopTailLitsTailStartReader_of_ge3
      (bw := bw) (remaining := remaining) (b := b)
      (tailBits := tailBits) (tailLen := tailLen) (hbit := hbit) (hrem := hrem)
  rw [hreaderGe]
  dsimp [dist1ChunkLoopTailLitsTailStartReaderStep]
  let chunk := chooseFixedMatchChunkLen remaining
  let rem' := remaining - chunk
  let remLit' := dist1ChunkLoopRem rem'
  let litTail' := literalRepeatBitsTail b remLit' tailBits tailLen
  let restBits := dist1ChunkLoopBitsTail rem' litTail'.1 litTail'.2
  let chunkInfo := fixedLenMatchInfo chunk
  let sym := chunkInfo.1
  let extraBits := chunkInfo.2.1
  let extraLen := chunkInfo.2.2
  let codeLen := fixedLitLenCode sym
  let symBits := reverseBits codeLen.1 codeLen.2
  let distBitsTot := (0 : Nat) ||| (restBits.1 <<< 5)
  let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
  let bitsTot := symBits ||| (lenBitsTot <<< codeLen.2)
  let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
  let bw2 := BitWriter.writeBits bw1 lenBitsTot extraLen
  let bwChunk := BitWriter.writeBits bw2 distBitsTot 5
  let hbit1 := bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit
  let hbit2 := bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1
  let hbitChunk := bitPos_lt_8_writeBits bw2 distBitsTot 5 hbit2
  have hchunk : 3 ≤ chunk ∧ chunk ≤ 258 := by
    have hbounds := chooseFixedMatchChunkLen_bounds remaining hrem
    exact ⟨by simpa [chunk] using hbounds.1, by simpa [chunk] using hbounds.2.1⟩
  have hinfo :=
    fixedLenMatchInfo_spec_get! chunk hchunk.1 hchunk.2
  have hsymBitsLt : symBits < 2 ^ codeLen.2 := by
    dsimp [symBits]
    simpa using (reverseBits_lt codeLen.1 codeLen.2)
  have hextraBitsLt : extraBits < 2 ^ extraLen := by
    simpa [chunkInfo, sym, extraBits, extraLen] using hinfo.2.2.2.2
  have hbw1 :
      bw1 = BitWriter.writeBits bw symBits codeLen.2 := by
    dsimp [bw1, bitsTot]
    exact writeBits_or_shift_tail bw symBits lenBitsTot codeLen.2 hsymBitsLt
  have hbw2 :
      bw2 = BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen := by
    dsimp [bw2, lenBitsTot]
    rw [hbw1]
    exact writeBits_or_shift_tail (BitWriter.writeBits bw symBits codeLen.2)
      extraBits distBitsTot extraLen hextraBitsLt
  have hmatchEq : bw.writeFixedMatchDist1Fast chunk = bwChunk := by
    calc
      bw.writeFixedMatchDist1Fast chunk =
          BitWriter.writeBits
            (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen) 0 5 := by
            simpa [chunkInfo, sym, extraBits, extraLen, codeLen, symBits] using
              (writeFixedMatchDist1Fast_eq_writeBits_chain (bw := bw) (matchLen := chunk) (hlen := hchunk))
      _ = BitWriter.writeBits bw2 0 5 := by rw [hbw2]
      _ = bwChunk := by
            dsimp [bwChunk]
            symm
            simpa [distBitsTot] using
              (writeBits_or_shift_tail bw2 0 restBits.1 5 (by decide))
  have hdef :
      bw.writeFixedMatchDist1ChunksFast remaining =
        bwChunk.writeFixedMatchDist1ChunksFast rem' := by
    rw [BitWriter.writeFixedMatchDist1ChunksFast.eq_1]
    simp [hrem, chunk, rem', hmatchEq, bw1, bw2, bwChunk]
  rcases chooseFixedMatchChunkLen_sub_zero_or_ge3 remaining hrem with hzero | hrem'
  · have hrem0 : rem' = 0 := by
      simpa [rem'] using hzero
    have hremLt : ¬ 3 ≤ rem' := by
      rw [hrem0]
      decide
    have hreader0 :
        dist1ChunkLoopTailLitsTailStartReader bwChunk rem' b tailBits tailLen hbitChunk =
          literalRepeatTailStartReader bwChunk b rem' tailBits tailLen hbitChunk := by
      exact dist1ChunkLoopTailLitsTailStartReader_of_lt3
        (bw := bwChunk) (remaining := rem') (b := b)
        (tailBits := tailBits) (tailLen := tailLen) (hbit := hbitChunk) (hrem := hremLt)
    have hwriter0 : bwChunk.writeFixedMatchDist1ChunksFast rem' = bwChunk := by
      rw [hrem0]
      simp [BitWriter.writeFixedMatchDist1ChunksFast]
    calc
      dist1ChunkLoopTailLitsTailStartReader bwChunk rem' b tailBits tailLen hbitChunk
          = literalRepeatTailStartReader bwChunk b rem' tailBits tailLen hbitChunk := hreader0
      _ = literalRepeatTailStartReader bwChunk b 0 tailBits tailLen hbitChunk := by
            simp [hrem0]
      _ =
          BitWriter.readerAt bwChunk
            (BitWriter.writeBits bwChunk tailBits tailLen).flush
            (flush_size_writeBits_le bwChunk tailBits tailLen) hbitChunk := by
            simpa using literalRepeatTailStartReader_eq_runtimeStartReader
              bwChunk b 0 tailBits tailLen hbitChunk
      _ =
          BitWriter.readerAt (bwChunk.writeFixedMatchDist1ChunksFast rem')
            (BitWriter.writeBits (bwChunk.writeFixedMatchDist1ChunksFast rem') tailBits tailLen).flush
            (flush_size_writeBits_le (bwChunk.writeFixedMatchDist1ChunksFast rem') tailBits tailLen)
            (writeFixedMatchDist1ChunksFast_bitPos_lt bwChunk rem' hbitChunk) := by
            exact (readerAt_writeBits_eq_of_writer_eq
              (h := hwriter0) (tailBits := tailBits) (tailLen := tailLen)
              (hbit1 := writeFixedMatchDist1ChunksFast_bitPos_lt bwChunk rem' hbitChunk)
              (hbit2 := hbitChunk)).symm
      _ =
          BitWriter.readerAt (bw.writeFixedMatchDist1ChunksFast remaining)
            (BitWriter.writeBits (bw.writeFixedMatchDist1ChunksFast remaining) tailBits tailLen).flush
            (flush_size_writeBits_le (bw.writeFixedMatchDist1ChunksFast remaining) tailBits tailLen)
            (writeFixedMatchDist1ChunksFast_bitPos_lt bw remaining hbit) := by
            exact readerAt_writeBits_eq_of_writer_eq
              (h := hdef.symm) (tailBits := tailBits) (tailLen := tailLen)
              (hbit1 := writeFixedMatchDist1ChunksFast_bitPos_lt bwChunk rem' hbitChunk)
              (hbit2 := writeFixedMatchDist1ChunksFast_bitPos_lt bw remaining hbit)
  · have hlt : rem' < remaining := by
      simpa [chunk, rem'] using (chooseFixedMatchChunkLen_sub_lt remaining hrem)
    have hih :=
      ih rem' hlt bwChunk b tailBits tailLen hbitChunk hrem'
    calc
      dist1ChunkLoopTailLitsTailStartReader bwChunk rem' b tailBits tailLen hbitChunk
          =
        BitWriter.readerAt (bwChunk.writeFixedMatchDist1ChunksFast rem')
          (BitWriter.writeBits (bwChunk.writeFixedMatchDist1ChunksFast rem') tailBits tailLen).flush
          (flush_size_writeBits_le (bwChunk.writeFixedMatchDist1ChunksFast rem') tailBits tailLen)
          (writeFixedMatchDist1ChunksFast_bitPos_lt bwChunk rem' hbitChunk) := hih
      _ =
        BitWriter.readerAt (bw.writeFixedMatchDist1ChunksFast remaining)
          (BitWriter.writeBits (bw.writeFixedMatchDist1ChunksFast remaining) tailBits tailLen).flush
          (flush_size_writeBits_le (bw.writeFixedMatchDist1ChunksFast remaining) tailBits tailLen)
          (writeFixedMatchDist1ChunksFast_bitPos_lt bw remaining hbit) := by
          exact readerAt_writeBits_eq_of_writer_eq
            (h := hdef.symm) (tailBits := tailBits) (tailLen := tailLen)
            (hbit1 := writeFixedMatchDist1ChunksFast_bitPos_lt bwChunk rem' hbitChunk)
            (hbit2 := writeFixedMatchDist1ChunksFast_bitPos_lt bw remaining hbit)

lemma decodeFixedBlockFuelFast_dist1Run_readerAt_writeBits_tail
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (remaining tailBits tailLen : Nat) (out : ByteArray)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bwLit := BitWriter.writeFixedLiteralFast bw b
    decodeFixedBlockFuelFast (fuel + dist1RunSteps remaining)
      (BitWriter.readerAt bw
        (BitWriter.writeBits bw (dist1RunBitsTail b remaining tailBits tailLen).1
          (dist1RunBitsTail b remaining tailBits tailLen).2).flush
        (flush_size_writeBits_le bw
          (dist1RunBitsTail b remaining tailBits tailLen).1
          (dist1RunBitsTail b remaining tailBits tailLen).2) hbit) out =
      decodeFixedBlockFuelFast fuel
        (dist1ChunkLoopTailLitsTailStartReader bwLit remaining b tailBits tailLen
          (writeFixedLiteralFast_bitPos_lt bw b hbit))
        (dist1RunOut out b remaining) := by
  let remLit := dist1ChunkLoopRem remaining
  let litTail := literalRepeatBitsTail b remLit tailBits tailLen
  let chunkBits := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
  let bwLit := BitWriter.writeFixedLiteralFast bw b
  have htail2Lit : 2 ≤ litTail.2 := by
    dsimp [litTail]
    exact literalRepeatBitsTail_len_ge_two b remLit tailBits tailLen htail2
  have htail2Chunk : 2 ≤ chunkBits.2 := by
    dsimp [chunkBits]
    exact le_trans htail2Lit (dist1ChunkLoopBitsTail_len_ge remaining litTail.1 litTail.2)
  have hbitLit : bwLit.bitPos < 8 := by
    dsimp [bwLit]
    exact writeFixedLiteralFast_bitPos_lt bw b hbit
  have hcurLit : bwLit.curClearAbove := by
    dsimp [bwLit]
    exact writeFixedLiteralFast_curClearAbove bw b hbit hcur
  have hstep :=
    decodeFixedBlockFuelFast_step_literal_readerAt_writeBits_tail
      (fuel := fuel + dist1ChunkLoopSteps remaining + remLit)
      (bw := bw) (b := b) (tailBits := chunkBits.1) (tailLen := chunkBits.2)
      (out := out) (htail2 := htail2Chunk) (hbit := hbit) (hcur := hcur)
  have htail :=
    decodeFixedBlockFuelFast_dist1ChunkLoopTailLits_readerAt_writeBits_tail
      (fuel := fuel) (bw := bwLit) (remaining := remaining)
      (tailBits := tailBits) (tailLen := tailLen) (out := out.push b) (b := b)
      (hout := by simp) (hlast := by simpa [ByteArray.size_push] using get!_last_push out b) (htail2 := htail2)
      (hbit := hbitLit) (hcur := hcurLit)
  have hstart :
      literalTailStartReader bw b chunkBits.1 chunkBits.2 hbit =
        BitWriter.readerAt bwLit
          (BitWriter.writeBits bwLit chunkBits.1 chunkBits.2).flush
          (flush_size_writeBits_le bwLit chunkBits.1 chunkBits.2) hbitLit := by
    simpa [bwLit] using
      literalTailStartReader_eq_runtimeStartReader bw b chunkBits.1 chunkBits.2 hbit
  calc
    decodeFixedBlockFuelFast (fuel + dist1RunSteps remaining)
        (BitWriter.readerAt bw
          (BitWriter.writeBits bw (dist1RunBitsTail b remaining tailBits tailLen).1
            (dist1RunBitsTail b remaining tailBits tailLen).2).flush
          (flush_size_writeBits_le bw
            (dist1RunBitsTail b remaining tailBits tailLen).1
            (dist1RunBitsTail b remaining tailBits tailLen).2) hbit) out
        =
      decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit)
        (literalTailStartReader bw b chunkBits.1 chunkBits.2 hbit) (out.push b) := by
          simpa [dist1RunBitsTail, dist1RunSteps, remLit, litTail, chunkBits,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
    _ =
      decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit)
        (BitWriter.readerAt bwLit
          (BitWriter.writeBits bwLit chunkBits.1 chunkBits.2).flush
          (flush_size_writeBits_le bwLit chunkBits.1 chunkBits.2) hbitLit) (out.push b) := by
          simp [hstart]
    _ =
      decodeFixedBlockFuelFast fuel
        (dist1ChunkLoopTailLitsTailStartReader bwLit remaining b tailBits tailLen hbitLit)
        (pushRepeat (out.push b) b remaining) := by
          simpa [remLit, litTail, chunkBits] using htail
    _ =
      decodeFixedBlockFuelFast fuel
        (dist1ChunkLoopTailLitsTailStartReader bwLit remaining b tailBits tailLen hbitLit)
        (dist1RunOut out b remaining) := by
          simp [dist1RunOut]

lemma sameByteRunEndFast_ge (data : Array UInt8) (b : UInt8) (j : Nat) :
    j ≤ sameByteRunEndFast data b j := by
  simpa [sameByteRunEndFast_eq_sameByteRunEnd] using sameByteRunEnd_ge data b j

lemma sameByteRunEndFast_le_size (data : Array UInt8) (b : UInt8) (j : Nat)
    (hj : j ≤ data.size) :
    sameByteRunEndFast data b j ≤ data.size := by
  simpa [sameByteRunEndFast_eq_sameByteRunEnd] using
    sameByteRunEnd_le_size data b j hj

lemma sameByteRunEndFast_gt_prev
    (data : Array UInt8) (i : Nat) (h : i < data.size) :
    i < sameByteRunEndFast data data[i] (i + 1) := by
  simpa [sameByteRunEndFast_eq_sameByteRunEnd] using
    sameByteRunEnd_gt_prev data i h

def fixedRunFastBitsEob (data : Array UInt8) (i : Nat) : Nat × Nat :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEndFast data b (i + 1)
    let runLen := j - i
    let tail := fixedRunFastBitsEob data j
    if 4 ≤ runLen then
      dist1RunBitsTail b (runLen - 1) tail.1 tail.2
    else
      literalRepeatBitsTail b runLen tail.1 tail.2
  else
    let eob := fixedLitLenCode 256
    (reverseBits eob.1 eob.2, eob.2)
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  let j := sameByteRunEndFast data data[i] (i + 1)
  have hgt : i < j := by
    exact sameByteRunEndFast_gt_prev data i hlt
  have hle : j ≤ data.size := by
    exact sameByteRunEndFast_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  omega

def fixedRunFastStepsEob (data : Array UInt8) (i : Nat) : Nat :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEndFast data b (i + 1)
    let runLen := j - i
    let tail := fixedRunFastStepsEob data j
    if 4 ≤ runLen then
      dist1RunSteps (runLen - 1) + tail
    else
      runLen + tail
  else
    1
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  let j := sameByteRunEndFast data data[i] (i + 1)
  have hgt : i < j := by
    exact sameByteRunEndFast_gt_prev data i hlt
  have hle : j ≤ data.size := by
    exact sameByteRunEndFast_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  omega

private lemma fixedRunFastBitsEob_of_match
    (data : Array UInt8) (i : Nat) (b : UInt8) (j runLen tailBits tailLen : Nat)
    (hlt : i < data.size)
    (hb : b = data[i])
    (hj : j = sameByteRunEndFast data b (i + 1))
    (hrun : runLen = j - i)
    (htailBits : tailBits = (fixedRunFastBitsEob data j).1)
    (htailLen : tailLen = (fixedRunFastBitsEob data j).2)
    (h4 : 4 ≤ runLen) :
    fixedRunFastBitsEob data i =
      dist1RunBitsTail b (runLen - 1) tailBits tailLen := by
  have h4' : 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i := by
    simpa [hb, hj, hrun] using h4
  rw [fixedRunFastBitsEob.eq_1]
  simp [hlt, hb, hj, hrun, htailBits, htailLen, h4']

private lemma fixedRunFastBitsEob_of_literal
    (data : Array UInt8) (i : Nat) (b : UInt8) (j runLen tailBits tailLen : Nat)
    (hlt : i < data.size)
    (hb : b = data[i])
    (hj : j = sameByteRunEndFast data b (i + 1))
    (hrun : runLen = j - i)
    (htailBits : tailBits = (fixedRunFastBitsEob data j).1)
    (htailLen : tailLen = (fixedRunFastBitsEob data j).2)
    (h4 : ¬ 4 ≤ runLen) :
    fixedRunFastBitsEob data i =
      literalRepeatBitsTail b runLen tailBits tailLen := by
  have h4' : ¬ 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i := by
    simpa [hb, hj, hrun] using h4
  rw [fixedRunFastBitsEob.eq_1]
  simp [hlt, hb, hj, hrun, htailBits, htailLen, h4']

private lemma fixedRunFastStepsEob_of_match
    (data : Array UInt8) (i : Nat) (b : UInt8) (j runLen : Nat)
    (hlt : i < data.size)
    (hb : b = data[i])
    (hj : j = sameByteRunEndFast data b (i + 1))
    (hrun : runLen = j - i)
    (h4 : 4 ≤ runLen) :
    fixedRunFastStepsEob data i =
      dist1RunSteps (runLen - 1) + fixedRunFastStepsEob data j := by
  have h4' : 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i := by
    simpa [hb, hj, hrun] using h4
  rw [fixedRunFastStepsEob.eq_1]
  simp [hlt, hb, hj, hrun, h4']

private lemma fixedRunFastStepsEob_of_literal
    (data : Array UInt8) (i : Nat) (b : UInt8) (j runLen : Nat)
    (hlt : i < data.size)
    (hb : b = data[i])
    (hj : j = sameByteRunEndFast data b (i + 1))
    (hrun : runLen = j - i)
    (h4 : ¬ 4 ≤ runLen) :
    fixedRunFastStepsEob data i =
      runLen + fixedRunFastStepsEob data j := by
  have h4' : ¬ 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i := by
    simpa [hb, hj, hrun] using h4
  rw [fixedRunFastStepsEob.eq_1]
  simp [hlt, hb, hj, hrun, h4']

def fixedRunFastOut (data : Array UInt8) (i : Nat) (out : ByteArray) : ByteArray :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEndFast data b (i + 1)
    let runLen := j - i
    let out' :=
      if 4 ≤ runLen then
        dist1RunOut out b (runLen - 1)
      else
        pushRepeat out b runLen
    fixedRunFastOut data j out'
  else
    out
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  let j := sameByteRunEndFast data data[i] (i + 1)
  have hgt : i < j := by
    exact sameByteRunEndFast_gt_prev data i hlt
  have hle : j ≤ data.size := by
    exact sameByteRunEndFast_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  omega

lemma fixedRunFastOut_eq_byteArrayFromArray (data : Array UInt8) (i : Nat) (out : ByteArray) :
    fixedRunFastOut data i out = byteArrayFromArray data i out := by
  classical
  by_cases hlt : i < data.size
  · rw [fixedRunFastOut.eq_1]
    simp [hlt]
    let b := data[i]
    let jFast := sameByteRunEndFast data b (i + 1)
    let j := sameByteRunEnd data b (i + 1)
    let runLen := jFast - i
    have hnext : sameByteRunEnd data data[i] (i + 1) = j := by
      simp [b, j]
    have hrun : sameByteRunEndFast data data[i] (i + 1) - i = runLen := by
      simp [b, jFast, runLen]
    have hsame : jFast = j := by
      simpa [jFast, j] using sameByteRunEndFast_eq_sameByteRunEnd data b (i + 1)
    have hscan0 : sameByteRunEnd data b i = j := by
      rw [sameByteRunEnd.eq_def]
      simp [hlt, b, hnext]
    have hrunScan : sameByteRunEnd data b i - i = runLen := by
      calc
        sameByteRunEnd data b i - i = j - i := by simp [hscan0]
        _ = runLen := by simp [runLen, hsame]
    have hbaRun :
        byteArrayFromArray data i out =
          byteArrayFromArray data j (pushRepeat out b runLen) := by
      have htmp := byteArrayFromArray_sameByteRunEnd_pushRepeat data b i out
      calc
        byteArrayFromArray data i out
            = byteArrayFromArray data (sameByteRunEnd data b i)
                (pushRepeat out b (sameByteRunEnd data b i - i)) := htmp
        _ = byteArrayFromArray data j
              (pushRepeat out b (sameByteRunEnd data b i - i)) := by
                simp [hscan0]
        _ = byteArrayFromArray data j (pushRepeat out b runLen) := by
              simp [hrunScan]
    by_cases h4 : 4 ≤ runLen
    · have hih :
          fixedRunFastOut data jFast (dist1RunOut out b (runLen - 1)) =
            byteArrayFromArray data jFast (dist1RunOut out b (runLen - 1)) := by
        exact fixedRunFastOut_eq_byteArrayFromArray data jFast (dist1RunOut out b (runLen - 1))
      have haccEq : dist1RunOut out b (runLen - 1) = pushRepeat out b runLen := by
        calc
          dist1RunOut out b (runLen - 1) = pushRepeat out b ((runLen - 1) + 1) := by
            simpa using dist1RunOut_eq_pushRepeat out b (runLen - 1)
          _ = pushRepeat out b runLen := by
            have harrith : (runLen - 1) + 1 = runLen := by omega
            simp [harrith]
      have hmid :
          fixedRunFastOut data (sameByteRunEndFast data data[i] (i + 1))
            (if 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i then
              dist1RunOut out data[i] (sameByteRunEndFast data data[i] (i + 1) - i - 1)
            else
              pushRepeat out data[i] (sameByteRunEndFast data data[i] (i + 1) - i)) =
            byteArrayFromArray data i out := by
        calc
          fixedRunFastOut data (sameByteRunEndFast data data[i] (i + 1))
              (if 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i then
                dist1RunOut out data[i] (sameByteRunEndFast data data[i] (i + 1) - i - 1)
              else
                pushRepeat out data[i] (sameByteRunEndFast data data[i] (i + 1) - i))
              = fixedRunFastOut data jFast (dist1RunOut out b (runLen - 1)) := by
                  simp [b, jFast, runLen, h4, hrun]
          _ = byteArrayFromArray data jFast (dist1RunOut out b (runLen - 1)) := hih
          _ = byteArrayFromArray data j (dist1RunOut out b (runLen - 1)) := by
                simp [hsame]
          _ = byteArrayFromArray data j (pushRepeat out b runLen) := by
                simp [haccEq]
          _ = byteArrayFromArray data i out := hbaRun.symm
      exact hmid
    · have hih :
          fixedRunFastOut data jFast (pushRepeat out b runLen) =
            byteArrayFromArray data jFast (pushRepeat out b runLen) := by
        exact fixedRunFastOut_eq_byteArrayFromArray data jFast (pushRepeat out b runLen)
      have hmid :
          fixedRunFastOut data (sameByteRunEndFast data data[i] (i + 1))
            (if 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i then
              dist1RunOut out data[i] (sameByteRunEndFast data data[i] (i + 1) - i - 1)
            else
              pushRepeat out data[i] (sameByteRunEndFast data data[i] (i + 1) - i)) =
            byteArrayFromArray data i out := by
        calc
          fixedRunFastOut data (sameByteRunEndFast data data[i] (i + 1))
              (if 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i then
                dist1RunOut out data[i] (sameByteRunEndFast data data[i] (i + 1) - i - 1)
              else
                pushRepeat out data[i] (sameByteRunEndFast data data[i] (i + 1) - i))
              = fixedRunFastOut data jFast (pushRepeat out b runLen) := by
                  simp [b, jFast, runLen, h4, hrun]
          _ = byteArrayFromArray data jFast (pushRepeat out b runLen) := hih
          _ = byteArrayFromArray data j (pushRepeat out b runLen) := by
                simp [hsame]
          _ = byteArrayFromArray data i out := hbaRun.symm
      exact hmid
  · have hleft : fixedRunFastOut data i out = out := by
      simp [fixedRunFastOut, hlt]
    have hright : byteArrayFromArray data i out = out := by
      rw [byteArrayFromArray_unfold]
      simp [hlt]
    exact hleft.trans hright.symm
termination_by data.size - i
decreasing_by
  all_goals
    have hgt : i < sameByteRunEndFast data data[i] (i + 1) := by
      exact sameByteRunEndFast_gt_prev data i hlt
    have hle : sameByteRunEndFast data data[i] (i + 1) ≤ data.size := by
      exact sameByteRunEndFast_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
    omega

lemma fixedRunFastOut_eq_fixedRunScanOut (data : Array UInt8) (i : Nat) (out : ByteArray) :
    fixedRunFastOut data i out = fixedRunScanOut data i out := by
  calc
    fixedRunFastOut data i out = byteArrayFromArray data i out :=
      fixedRunFastOut_eq_byteArrayFromArray data i out
    _ = fixedRunScanOut data i out := by
      symm
      exact fixedRunScanOut_eq_byteArrayFromArray data i out

lemma fixedRunFastBitsEob_len_ge_two (data : Array UInt8) (i : Nat) :
    2 ≤ (fixedRunFastBitsEob data i).2 := by
  have hk :
      ∀ k, ∀ i, data.size - i = k → 2 ≤ (fixedRunFastBitsEob data i).2 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro i hk
        by_cases hlt : i < data.size
        · let b := data[i]
          let j := sameByteRunEndFast data b (i + 1)
          let runLen := j - i
          have hk' : data.size - j < k := by
            have hgt : i < j := by
              exact sameByteRunEndFast_gt_prev data i hlt
            have hlt' : data.size - j < data.size - i := by
              exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := j) hlt hgt
            simpa [j, hk] using hlt'
          have htail : 2 ≤ (fixedRunFastBitsEob data j).2 := by
            exact ih (data.size - j) hk' j rfl
          by_cases h4 : 4 ≤ runLen
          · have hrem : 3 ≤ runLen - 1 := by omega
            have hbits :
                fixedRunFastBitsEob data i =
                  dist1RunBitsTail b (runLen - 1)
                    (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2 := by
              exact fixedRunFastBitsEob_of_match data i b j runLen
                (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2
                hlt rfl rfl rfl rfl rfl h4
            rw [hbits]
            exact dist1RunBitsTail_len_ge_two b (runLen - 1) _ _ htail
          · have hbits :
                fixedRunFastBitsEob data i =
                  literalRepeatBitsTail b runLen
                    (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2 := by
              exact fixedRunFastBitsEob_of_literal data i b j runLen
                (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2
                hlt rfl rfl rfl rfl rfl h4
            rw [hbits]
            exact literalRepeatBitsTail_len_ge_two b runLen _ _ htail
        · have hbits : (fixedRunFastBitsEob data i).2 = (fixedLitLenCode 256).2 := by
            rw [fixedRunFastBitsEob.eq_1]
            simp [hlt]
          rw [hbits]
          decide
  exact hk (data.size - i) i rfl

lemma literalRepeatBitsTail_len_ge_steps
    (b : UInt8) (n tailBits tailLen : Nat) :
    n + tailLen ≤ (literalRepeatBitsTail b n tailBits tailLen).2 := by
  induction n generalizing tailBits tailLen with
  | zero =>
      simp [literalRepeatBitsTail_zero]
  | succ n ih =>
      let rest := literalRepeatBitsTail b n tailBits tailLen
      have hrest : n + tailLen ≤ rest.2 := by
        simpa [rest] using ih (tailBits := tailBits) (tailLen := tailLen)
      have hlen : 1 ≤ (fixedLitLenCode b.toNat).2 := by
        exact fixedLitLenCode_len_pos b.toNat (lt_trans (UInt8.toNat_lt b) (by decide))
      have hstep :
          n + tailLen + 1 ≤ (fixedLitLenCode b.toNat).2 + rest.2 := by
        omega
      simpa [literalRepeatBitsTail_succ, rest, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using hstep

lemma dist1ChunkLoopBitsTail_len_ge_steps
    (remaining tailBits tailLen : Nat) :
    dist1ChunkLoopSteps remaining + tailLen ≤ (dist1ChunkLoopBitsTail remaining tailBits tailLen).2 := by
  have hk :
      ∀ k, ∀ remaining tailBits tailLen, remaining = k →
        dist1ChunkLoopSteps remaining + tailLen ≤ (dist1ChunkLoopBitsTail remaining tailBits tailLen).2 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro remaining tailBits tailLen hk
        by_cases h : 3 ≤ remaining
        · let chunk := chooseFixedMatchChunkLen remaining
          let rem' := remaining - chunk
          let rest := dist1ChunkLoopBitsTail rem' tailBits tailLen
          have hlt : rem' < k := by
            have hsub : rem' < remaining := by
              simpa [chunk, rem'] using (chooseFixedMatchChunkLen_sub_lt remaining h)
            simpa [hk] using hsub
          have hrest : dist1ChunkLoopSteps rem' + tailLen ≤ rest.2 := by
            exact ih rem' hlt rem' tailBits tailLen rfl
          have hstep : dist1ChunkLoopSteps remaining = 1 + dist1ChunkLoopSteps rem' := by
            simpa [chunk, rem'] using (dist1ChunkLoopSteps_of_ge3 remaining h)
          rw [dist1ChunkLoopBitsTail_of_ge3 remaining tailBits tailLen h]
          let info := fixedLenMatchInfo chunk
          let sym := info.1
          let extraLen := info.2.2
          let codeLen := fixedLitLenCode sym
          have hchunk : 3 ≤ chunk ∧ chunk ≤ 258 := by
            have hbounds := chooseFixedMatchChunkLen_bounds remaining h
            exact ⟨by simpa [chunk] using hbounds.1, by simpa [chunk] using hbounds.2.1⟩
          have hinfo := fixedLenMatchInfo_spec_get! chunk hchunk.1 hchunk.2
          have hsymLt : sym < 288 := by
            have hsymLe : sym ≤ 285 := by
              simpa [info, sym] using hinfo.2.1
            omega
          have hrest' : dist1ChunkLoopSteps rem' + tailLen ≤ rest.2 := by
            simpa [rest] using hrest
          have hcode : 1 ≤ codeLen.2 := by
            exact fixedLitLenCode_len_pos sym hsymLt
          rw [hstep]
          have hrest'' : 1 + dist1ChunkLoopSteps rem' + tailLen ≤ 1 + rest.2 := by
            simpa [Nat.add_assoc] using Nat.add_le_add_left hrest' 1
          calc
            1 + dist1ChunkLoopSteps rem' + tailLen ≤ 1 + rest.2 := hrest''
            _ ≤ codeLen.2 + rest.2 := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (Nat.add_le_add_right hcode rest.2)
            _ ≤ codeLen.2 + (extraLen + (5 + rest.2)) := by
              have htail : rest.2 ≤ extraLen + (5 + rest.2) := by
                calc
                  rest.2 ≤ 5 + rest.2 := Nat.le_add_left _ _
                  _ ≤ extraLen + (5 + rest.2) := Nat.le_add_left _ _
              exact Nat.add_le_add_left htail codeLen.2
        · simp [dist1ChunkLoopSteps_of_lt3 remaining h, dist1ChunkLoopBitsTail_of_lt3 remaining tailBits tailLen h]
  exact hk remaining remaining tailBits tailLen rfl

lemma dist1RunBitsTail_len_ge_steps
    (b : UInt8) (remaining tailBits tailLen : Nat) (hrem : 3 ≤ remaining) :
    dist1RunSteps remaining + tailLen ≤ (dist1RunBitsTail b remaining tailBits tailLen).2 := by
  let remLit := dist1ChunkLoopRem remaining
  let chunkBits := dist1ChunkLoopBitsTail remaining tailBits tailLen
  have hremLit0 : remLit = 0 := by
    dsimp [remLit]
    exact dist1ChunkLoopRem_eq_zero_of_ge3 remaining hrem
  have hchunk :
      dist1ChunkLoopSteps remaining + tailLen ≤ chunkBits.2 := by
    simpa [chunkBits] using dist1ChunkLoopBitsTail_len_ge_steps remaining tailBits tailLen
  have hlen : 1 ≤ (fixedLitLenCode b.toNat).2 := by
    exact fixedLitLenCode_len_pos b.toNat (lt_trans (UInt8.toNat_lt b) (by decide))
  rw [show dist1RunBitsTail b remaining tailBits tailLen =
      let codeLen := fixedLitLenCode b.toNat
      let bits := reverseBits codeLen.1 codeLen.2
      let bitsTot := bits ||| (chunkBits.1 <<< codeLen.2)
      let lenTot := codeLen.2 + chunkBits.2
      (bitsTot, lenTot) by
        simp [dist1RunBitsTail, remLit, hremLit0, literalRepeatBitsTail_zero, chunkBits]]
  have hstep : dist1RunSteps remaining = 1 + dist1ChunkLoopSteps remaining := by
    simp [dist1RunSteps, remLit, hremLit0]
  rw [hstep]
  calc
    1 + dist1ChunkLoopSteps remaining + tailLen ≤ 1 + chunkBits.2 := by
      have := Nat.add_le_add_left hchunk 1
      simpa [Nat.add_assoc] using this
    _ ≤ (fixedLitLenCode b.toNat).2 + chunkBits.2 := by
      exact Nat.add_le_add_right hlen chunkBits.2

lemma fixedRunFastStepsEob_le_fixedRunFastBitsEob_len (data : Array UInt8) (i : Nat) :
    fixedRunFastStepsEob data i ≤ (fixedRunFastBitsEob data i).2 := by
  have hk :
      ∀ k, ∀ i, data.size - i = k →
        fixedRunFastStepsEob data i ≤ (fixedRunFastBitsEob data i).2 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro i hk
        by_cases hlt : i < data.size
        · let b := data[i]
          let j := sameByteRunEndFast data b (i + 1)
          let runLen := j - i
          have hk' : data.size - j < k := by
            have hgt : i < j := by
              exact sameByteRunEndFast_gt_prev data i hlt
            have hlt' : data.size - j < data.size - i := by
              exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := j) hlt hgt
            simpa [j, hk] using hlt'
          have htail : fixedRunFastStepsEob data j ≤ (fixedRunFastBitsEob data j).2 := by
            exact ih (data.size - j) hk' j rfl
          by_cases h4 : 4 ≤ runLen
          · have hrem : 3 ≤ runLen - 1 := by omega
            have hsteps :
                fixedRunFastStepsEob data i =
                  dist1RunSteps (runLen - 1) + fixedRunFastStepsEob data j := by
              exact fixedRunFastStepsEob_of_match data i b j runLen
                hlt rfl rfl rfl h4
            have hbits :
                fixedRunFastBitsEob data i =
                  dist1RunBitsTail b (runLen - 1)
                    (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2 := by
              exact fixedRunFastBitsEob_of_match data i b j runLen
                (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2
                hlt rfl rfl rfl rfl rfl h4
            have hdist :
                dist1RunSteps (runLen - 1) + (fixedRunFastBitsEob data j).2 ≤
                  (dist1RunBitsTail b (runLen - 1)
                    (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2).2 := by
              simpa using
                dist1RunBitsTail_len_ge_steps b (runLen - 1)
                  (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2 hrem
            calc
              fixedRunFastStepsEob data i
                  = dist1RunSteps (runLen - 1) + fixedRunFastStepsEob data j := hsteps
              _ ≤ dist1RunSteps (runLen - 1) + (fixedRunFastBitsEob data j).2 := by omega
              _ ≤ (dist1RunBitsTail b (runLen - 1)
                    (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2).2 := hdist
              _ = (fixedRunFastBitsEob data i).2 := by rw [hbits]
          · have hsteps :
                fixedRunFastStepsEob data i =
                  runLen + fixedRunFastStepsEob data j := by
              exact fixedRunFastStepsEob_of_literal data i b j runLen
                hlt rfl rfl rfl h4
            have hbits :
                fixedRunFastBitsEob data i =
                  literalRepeatBitsTail b runLen
                    (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2 := by
              exact fixedRunFastBitsEob_of_literal data i b j runLen
                (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2
                hlt rfl rfl rfl rfl rfl h4
            have hlit :
                runLen + (fixedRunFastBitsEob data j).2 ≤
                  (literalRepeatBitsTail b runLen
                    (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2).2 := by
              simpa using
                literalRepeatBitsTail_len_ge_steps b runLen
                  (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2
            calc
              fixedRunFastStepsEob data i = runLen + fixedRunFastStepsEob data j := hsteps
              _ ≤ runLen + (fixedRunFastBitsEob data j).2 := by omega
              _ ≤ (literalRepeatBitsTail b runLen
                    (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2).2 := hlit
              _ = (fixedRunFastBitsEob data i).2 := by rw [hbits]
        · have hsteps : fixedRunFastStepsEob data i = 1 := by
            rw [fixedRunFastStepsEob.eq_1]
            simp [hlt]
          have hbits : (fixedRunFastBitsEob data i).2 = (fixedLitLenCode 256).2 := by
            rw [fixedRunFastBitsEob.eq_1]
            simp [hlt]
          rw [hsteps, hbits]
          decide
  exact hk (data.size - i) i rfl

private def fixedRunMatchNextWriter (bw : BitWriter) (b : UInt8) (runLen : Nat) : BitWriter :=
  (BitWriter.writeFixedLiteralFast bw b).writeFixedMatchDist1ChunksFast (runLen - 1)

private def fixedRunLiteralNextWriter (bw : BitWriter) (b : UInt8) (runLen : Nat) : BitWriter :=
  bw.writeFixedLiteralRepeatFast b runLen

private lemma fixedRunMatchNextWriter_bitPos_lt
    (bw : BitWriter) (b : UInt8) (runLen : Nat) (hbit : bw.bitPos < 8) :
    (fixedRunMatchNextWriter bw b runLen).bitPos < 8 := by
  dsimp [fixedRunMatchNextWriter]
  exact writeFixedMatchDist1ChunksFast_bitPos_lt
    (BitWriter.writeFixedLiteralFast bw b) (runLen - 1)
    (writeFixedLiteralFast_bitPos_lt bw b hbit)

private lemma fixedRunMatchNextWriter_curClearAbove
    (bw : BitWriter) (b : UInt8) (runLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (fixedRunMatchNextWriter bw b runLen).curClearAbove := by
  dsimp [fixedRunMatchNextWriter]
  exact writeFixedMatchDist1ChunksFast_curClearAbove
    (BitWriter.writeFixedLiteralFast bw b) (runLen - 1)
    (writeFixedLiteralFast_bitPos_lt bw b hbit)
    (writeFixedLiteralFast_curClearAbove bw b hbit hcur)

private lemma fixedRunLiteralNextWriter_bitPos_lt
    (bw : BitWriter) (b : UInt8) (runLen : Nat) (hbit : bw.bitPos < 8) :
    (fixedRunLiteralNextWriter bw b runLen).bitPos < 8 := by
  dsimp [fixedRunLiteralNextWriter]
  exact writeFixedLiteralRepeatFast_bitPos_lt bw b runLen hbit

private lemma fixedRunLiteralNextWriter_curClearAbove
    (bw : BitWriter) (b : UInt8) (runLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (fixedRunLiteralNextWriter bw b runLen).curClearAbove := by
  dsimp [fixedRunLiteralNextWriter]
  exact writeFixedLiteralRepeatFast_curClearAbove bw b runLen hbit hcur

private lemma deflateFixedRunAuxFast_of_match
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8) (j runLen : Nat)
    (hlt : i < data.size)
    (hb : b = data[i])
    (hj : j = sameByteRunEndFast data b (i + 1))
    (hrun : runLen = j - i)
    (h4 : 4 ≤ runLen) :
    deflateFixedRunAuxFast data i bw =
      deflateFixedRunAuxFast data j (fixedRunMatchNextWriter bw b runLen) := by
  have h4' : 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i := by
    simpa [hb, hj, hrun] using h4
  rw [deflateFixedRunAuxFast.eq_1]
  simp [hlt, hb, hj, hrun, h4', fixedRunMatchNextWriter]

private lemma deflateFixedRunAuxFast_of_literal
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8) (j runLen : Nat)
    (hlt : i < data.size)
    (hb : b = data[i])
    (hj : j = sameByteRunEndFast data b (i + 1))
    (hrun : runLen = j - i)
    (h4 : ¬ 4 ≤ runLen) :
    deflateFixedRunAuxFast data i bw =
      deflateFixedRunAuxFast data j (fixedRunLiteralNextWriter bw b runLen) := by
  have h4' : ¬ 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i := by
    simpa [hb, hj, hrun] using h4
  rw [deflateFixedRunAuxFast.eq_1]
  simp [hlt, hb, hj, hrun, h4', fixedRunLiteralNextWriter]

private lemma deflateFixedRunAuxFast_writeBits_match_branch
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8) (j runLen : Nat)
    (tailBits tailLen : Nat)
    (hbits :
      fixedRunFastBitsEob data i = dist1RunBitsTail b (runLen - 1) tailBits tailLen)
    (hbw1 :
      deflateFixedRunAuxFast data i bw =
        deflateFixedRunAuxFast data j (fixedRunMatchNextWriter bw b runLen))
    (hih :
      BitWriter.writeBits (fixedRunMatchNextWriter bw b runLen) tailBits tailLen =
        BitWriter.writeBits
          (deflateFixedRunAuxFast data j (fixedRunMatchNextWriter bw b runLen))
          (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
          (fixedLitLenCode 256).2)
    (hrem : 3 ≤ runLen - 1) :
    BitWriter.writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2 =
      BitWriter.writeBits
        (deflateFixedRunAuxFast data i bw)
        (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
        (fixedLitLenCode 256).2 := by
  calc
    BitWriter.writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2
        = BitWriter.writeBits (fixedRunMatchNextWriter bw b runLen) tailBits tailLen := by
            simpa [hbits, fixedRunMatchNextWriter] using
              (writeBits_dist1RunBitsTail (bw := bw) (b := b) (remaining := runLen - 1)
                (tailBits := tailBits) (tailLen := tailLen) hrem)
    _ = BitWriter.writeBits
          (deflateFixedRunAuxFast data j (fixedRunMatchNextWriter bw b runLen))
          (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
          (fixedLitLenCode 256).2 := hih
    _ = BitWriter.writeBits
          (deflateFixedRunAuxFast data i bw)
          (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
          (fixedLitLenCode 256).2 := by
            simp [hbw1]

private lemma deflateFixedRunAuxFast_writeBits_literal_branch
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (b : UInt8) (j runLen : Nat)
    (tailBits tailLen : Nat)
    (hbits :
      fixedRunFastBitsEob data i = literalRepeatBitsTail b runLen tailBits tailLen)
    (hbw1 :
      deflateFixedRunAuxFast data i bw =
        deflateFixedRunAuxFast data j (fixedRunLiteralNextWriter bw b runLen))
    (hih :
      BitWriter.writeBits (fixedRunLiteralNextWriter bw b runLen) tailBits tailLen =
        BitWriter.writeBits
          (deflateFixedRunAuxFast data j (fixedRunLiteralNextWriter bw b runLen))
          (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
          (fixedLitLenCode 256).2) :
    BitWriter.writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2 =
      BitWriter.writeBits
        (deflateFixedRunAuxFast data i bw)
        (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
        (fixedLitLenCode 256).2 := by
  calc
    BitWriter.writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2
        = BitWriter.writeBits (fixedRunLiteralNextWriter bw b runLen) tailBits tailLen := by
            simpa [hbits, fixedRunLiteralNextWriter] using
              (writeBits_literalRepeatBitsTail (bw := bw) (b := b) (n := runLen)
                (tailBits := tailBits) (tailLen := tailLen))
    _ = BitWriter.writeBits
          (deflateFixedRunAuxFast data j (fixedRunLiteralNextWriter bw b runLen))
          (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
          (fixedLitLenCode 256).2 := hih
    _ = BitWriter.writeBits
          (deflateFixedRunAuxFast data i bw)
          (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
          (fixedLitLenCode 256).2 := by
            simp [hbw1]

private def deflateFixedRunGoal (data : Array UInt8) (i : Nat) (bw : BitWriter) : Prop :=
  let bitsLen := fixedRunFastBitsEob data i
  let bw1 := deflateFixedRunAuxFast data i bw
  let eob := fixedLitLenCode 256
  BitWriter.writeBits bw bitsLen.1 bitsLen.2 =
    BitWriter.writeBits bw1 (reverseBits eob.1 eob.2) eob.2

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma deflateFixedRunAuxFast_writeBits (data : Array UInt8) (i : Nat) (bw : BitWriter) :
    deflateFixedRunGoal data i bw := by
  classical
  have hk :
      ∀ k, ∀ i bw, data.size - i = k → deflateFixedRunGoal data i bw := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro i bw hk
        by_cases hlt : i < data.size
        · let b := data[i]
          let j := sameByteRunEndFast data b (i + 1)
          let runLen := j - i
          have hk' : data.size - j < k := by
            have hgt : i < j := by
              exact sameByteRunEndFast_gt_prev data i hlt
            have hlt' : data.size - j < data.size - i := by
              exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := j) hlt hgt
            simpa [j, hk] using hlt'
          by_cases h4 : 4 ≤ runLen
          · let tailBits := (fixedRunFastBitsEob data j).1
            let tailLen := (fixedRunFastBitsEob data j).2
            let bwNext := fixedRunMatchNextWriter bw b runLen
            have hih :=
              ih (data.size - j) hk' (i := j) (bw := bwNext) rfl
            have hbits :
                fixedRunFastBitsEob data i =
                  dist1RunBitsTail b (runLen - 1) tailBits tailLen := by
              exact fixedRunFastBitsEob_of_match data i b j runLen tailBits tailLen
                hlt rfl rfl rfl rfl rfl h4
            have hbw1 :
                deflateFixedRunAuxFast data i bw =
                  deflateFixedRunAuxFast data j bwNext := by
              simpa [bwNext] using
                deflateFixedRunAuxFast_of_match data i bw b j runLen hlt rfl rfl rfl h4
            have hrem : 3 ≤ runLen - 1 := by omega
            simpa [deflateFixedRunGoal] using
              (deflateFixedRunAuxFast_writeBits_match_branch
                data i bw b j runLen tailBits tailLen hbits hbw1
                (by simpa [bwNext, tailBits, tailLen, deflateFixedRunGoal] using hih) hrem)
          · let tailBits := (fixedRunFastBitsEob data j).1
            let tailLen := (fixedRunFastBitsEob data j).2
            let bwNext := fixedRunLiteralNextWriter bw b runLen
            have hih :=
              ih (data.size - j) hk' (i := j) (bw := bwNext) rfl
            have hbits :
                fixedRunFastBitsEob data i =
                  literalRepeatBitsTail b runLen tailBits tailLen := by
              exact fixedRunFastBitsEob_of_literal data i b j runLen tailBits tailLen
                hlt rfl rfl rfl rfl rfl h4
            have hbw1 :
                deflateFixedRunAuxFast data i bw =
                  deflateFixedRunAuxFast data j bwNext := by
              simpa [bwNext] using
                deflateFixedRunAuxFast_of_literal data i bw b j runLen hlt rfl rfl rfl h4
            dsimp [deflateFixedRunGoal]
            exact deflateFixedRunAuxFast_writeBits_literal_branch
              data i bw b j runLen tailBits tailLen hbits hbw1
              (by simpa [bwNext, tailBits, tailLen, deflateFixedRunGoal] using hih)
        · simp [deflateFixedRunGoal, fixedRunFastBitsEob, deflateFixedRunAuxFast, hlt, fixedLitLenCode]
  exact hk (data.size - i) i bw rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma deflateFixedRunFast_eq_writeBits (raw : ByteArray) :
    let bw0 := BitWriter.empty
    let bw1 := bw0.writeBits 1 1
    let bw2 := bw1.writeBits 1 2
    let bitsLen := fixedRunFastBitsEob raw.data 0
    deflateFixedRunFast raw = (BitWriter.writeBits bw2 bitsLen.1 bitsLen.2).flush := by
  unfold deflateFixedRunFast
  have hbits :=
    deflateFixedRunAuxFast_writeBits raw.data 0
      (BitWriter.writeBits (BitWriter.writeBits BitWriter.empty 1 1) 1 2)
  simp [deflateFixedRunGoal] at hbits
  simpa using (congrArg BitWriter.flush hbits).symm

private lemma fixedRunFastOut_of_match
    (data : Array UInt8) (i : Nat) (out : ByteArray) (b : UInt8) (j runLen : Nat)
    (hlt : i < data.size)
    (hb : b = data[i])
    (hj : j = sameByteRunEndFast data b (i + 1))
    (hrun : runLen = j - i)
    (h4 : 4 ≤ runLen) :
    fixedRunFastOut data i out =
      fixedRunFastOut data j (dist1RunOut out b (runLen - 1)) := by
  have h4' : 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i := by
    simpa [hb, hj, hrun] using h4
  rw [fixedRunFastOut.eq_1]
  simp [hlt, hb, hj, hrun, h4']

private lemma fixedRunFastOut_of_literal
    (data : Array UInt8) (i : Nat) (out : ByteArray) (b : UInt8) (j runLen : Nat)
    (hlt : i < data.size)
    (hb : b = data[i])
    (hj : j = sameByteRunEndFast data b (i + 1))
    (hrun : runLen = j - i)
    (h4 : ¬ 4 ≤ runLen) :
    fixedRunFastOut data i out =
      fixedRunFastOut data j (pushRepeat out b runLen) := by
  have h4' : ¬ 4 ≤ sameByteRunEndFast data data[i] (i + 1) - i := by
    simpa [hb, hj, hrun] using h4
  rw [fixedRunFastOut.eq_1]
  simp [hlt, hb, hj, hrun, h4']

@[irreducible] def fixedRunStartReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (hbit : bw.bitPos < 8) : BitReader :=
  BitWriter.readerAt bw
    (BitWriter.writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2).flush
    (flush_size_writeBits_le bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2) hbit

@[irreducible] def fixedRunAfterReader
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (hbit : bw.bitPos < 8) : BitReader :=
  flushReader
    (BitWriter.writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2)
    (bitPos_lt_8_writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2 hbit)

private lemma fixedRunAfterReader_eq_of_write_eq
    (data : Array UInt8) (i j : Nat) (bw bw' : BitWriter)
    (hbit : bw.bitPos < 8) (hbit' : bw'.bitPos < 8)
    (hwrite :
      BitWriter.writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2 =
        BitWriter.writeBits bw' (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2) :
    fixedRunAfterReader data j bw' hbit' = fixedRunAfterReader data i bw hbit := by
  unfold fixedRunAfterReader
  exact flushReader_eq_of_writer_eq
    (h := hwrite.symm)
    (hbit1 := bitPos_lt_8_writeBits bw'
      (fixedRunFastBitsEob data j).1 (fixedRunFastBitsEob data j).2 hbit')
    (hbit2 := bitPos_lt_8_writeBits bw
      (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2 hbit)

private lemma some_fixedRunState_eq_of_eqs
    (data : Array UInt8) (i j : Nat) (bw bw' : BitWriter)
    (hbit : bw.bitPos < 8) (hbit' : bw'.bitPos < 8)
    (out out' : ByteArray)
    (hafter :
      fixedRunAfterReader data j bw' hbit' = fixedRunAfterReader data i bw hbit)
    (hout :
      fixedRunFastOut data i out = fixedRunFastOut data j out') :
    some (fixedRunAfterReader data j bw' hbit', fixedRunFastOut data j out') =
      some (fixedRunAfterReader data i bw hbit, fixedRunFastOut data i out) := by
  simp [hafter, hout]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private lemma decodeFixedBlockFuelFast_fixedRunFastBitsEob_exact
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedBlockFuelFast (fixedRunFastStepsEob data i)
      (fixedRunStartReader data i bw hbit) out =
      some (fixedRunAfterReader data i bw hbit, fixedRunFastOut data i out) := by
  have hk :
      ∀ k, ∀ (i : Nat) (bw : BitWriter) (out : ByteArray)
        (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove), data.size - i = k →
        decodeFixedBlockFuelFast (fixedRunFastStepsEob data i)
          (fixedRunStartReader data i bw hbit) out =
          some (fixedRunAfterReader data i bw hbit, fixedRunFastOut data i out) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro i bw out hbit hcur hk
        by_cases hlt : i < data.size
        · let b := data[i]
          let j := sameByteRunEndFast data b (i + 1)
          let runLen := j - i
          have hk' : data.size - j < k := by
            have hgt : i < j := by
              exact sameByteRunEndFast_gt_prev data i hlt
            have hlt' : data.size - j < data.size - i := by
              exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := j) hlt hgt
            simpa [j, hk] using hlt'
          by_cases h4 : 4 ≤ runLen
          · let tailBits := (fixedRunFastBitsEob data j).1
            let tailLen := (fixedRunFastBitsEob data j).2
            let bwNext := fixedRunMatchNextWriter bw b runLen
            have hsteps :
                fixedRunFastStepsEob data i =
                  dist1RunSteps (runLen - 1) + fixedRunFastStepsEob data j := by
              exact fixedRunFastStepsEob_of_match data i b j runLen hlt rfl rfl rfl h4
            have hbits :
                fixedRunFastBitsEob data i =
                  dist1RunBitsTail b (runLen - 1) tailBits tailLen := by
              exact fixedRunFastBitsEob_of_match data i b j runLen tailBits tailLen
                hlt rfl rfl rfl rfl rfl h4
            have hout :
                fixedRunFastOut data i out =
                  fixedRunFastOut data j (dist1RunOut out b (runLen - 1)) := by
              exact fixedRunFastOut_of_match data i out b j runLen hlt rfl rfl rfl h4
            have htail2 : 2 ≤ tailLen := by
              dsimp [tailLen]
              exact fixedRunFastBitsEob_len_ge_two data j
            have hrem : 3 ≤ runLen - 1 := by
              omega
            have hbitNext : bwNext.bitPos < 8 := by
              simpa [bwNext] using fixedRunMatchNextWriter_bitPos_lt bw b runLen hbit
            have hcurNext : bwNext.curClearAbove := by
              simpa [bwNext] using fixedRunMatchNextWriter_curClearAbove bw b runLen hbit hcur
            have hstep :=
              decodeFixedBlockFuelFast_dist1Run_readerAt_writeBits_tail
                (fuel := fixedRunFastStepsEob data j) (bw := bw) (b := b)
                (remaining := runLen - 1) (tailBits := tailBits) (tailLen := tailLen)
                (out := out) (htail2 := htail2) (hbit := hbit) (hcur := hcur)
            have hreaderRec :
                dist1ChunkLoopTailLitsTailStartReader
                    (BitWriter.writeFixedLiteralFast bw b)
                    (runLen - 1) b tailBits tailLen (writeFixedLiteralFast_bitPos_lt bw b hbit) =
                  fixedRunStartReader data j bwNext hbitNext := by
              simpa [fixedRunStartReader, bwNext, fixedRunMatchNextWriter] using
                dist1ChunkLoopTailLitsTailStartReader_eq_runtimeStartReader
                  (bw := BitWriter.writeFixedLiteralFast bw b) (remaining := runLen - 1)
                  (b := b) (tailBits := tailBits) (tailLen := tailLen)
                  (hbit := writeFixedLiteralFast_bitPos_lt bw b hbit) hrem
            have hrec :
                decodeFixedBlockFuelFast (fixedRunFastStepsEob data j)
                  (dist1ChunkLoopTailLitsTailStartReader
                    (BitWriter.writeFixedLiteralFast bw b)
                    (runLen - 1) b tailBits tailLen (writeFixedLiteralFast_bitPos_lt bw b hbit))
                  (dist1RunOut out b (runLen - 1)) =
                some (fixedRunAfterReader data j bwNext hbitNext,
                  fixedRunFastOut data j (dist1RunOut out b (runLen - 1))) := by
              rw [hreaderRec]
              exact ih (data.size - j) hk' j bwNext (dist1RunOut out b (runLen - 1))
                hbitNext hcurNext rfl
            have hwrite :
                BitWriter.writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2 =
                  BitWriter.writeBits bwNext tailBits tailLen := by
              simpa [hbits, bwNext, fixedRunMatchNextWriter] using
                (writeBits_dist1RunBitsTail
                  (bw := bw) (b := b) (remaining := runLen - 1)
                  (tailBits := tailBits) (tailLen := tailLen) hrem)
            have hafter :
                fixedRunAfterReader data j bwNext hbitNext =
                  fixedRunAfterReader data i bw hbit := by
              simpa [tailBits, tailLen] using
                fixedRunAfterReader_eq_of_write_eq
                  (data := data) (i := i) (j := j)
                  (bw := bw) (bw' := bwNext)
                  (hbit := hbit) (hbit' := hbitNext) hwrite
            calc
              decodeFixedBlockFuelFast (fixedRunFastStepsEob data i)
                  (fixedRunStartReader data i bw hbit) out
                  =
                decodeFixedBlockFuelFast (fixedRunFastStepsEob data j)
                  (dist1ChunkLoopTailLitsTailStartReader
                    (BitWriter.writeFixedLiteralFast bw b)
                    (runLen - 1) b tailBits tailLen (writeFixedLiteralFast_bitPos_lt bw b hbit))
                  (dist1RunOut out b (runLen - 1)) := by
                    simpa [fixedRunStartReader, hsteps, hbits,
                      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
              _ =
                some (fixedRunAfterReader data j bwNext hbitNext,
                  fixedRunFastOut data j (dist1RunOut out b (runLen - 1))) := hrec
              _ =
                some (fixedRunAfterReader data i bw hbit, fixedRunFastOut data i out) := by
                  exact some_fixedRunState_eq_of_eqs
                    (data := data) (i := i) (j := j)
                    (bw := bw) (bw' := bwNext)
                    (hbit := hbit) (hbit' := hbitNext)
                    (out := out) (out' := dist1RunOut out b (runLen - 1))
                    hafter hout
          · let tailBits := (fixedRunFastBitsEob data j).1
            let tailLen := (fixedRunFastBitsEob data j).2
            let bwNext := fixedRunLiteralNextWriter bw b runLen
            have hsteps :
                fixedRunFastStepsEob data i =
                  runLen + fixedRunFastStepsEob data j := by
              exact fixedRunFastStepsEob_of_literal data i b j runLen hlt rfl rfl rfl h4
            have hbits :
                fixedRunFastBitsEob data i =
                  literalRepeatBitsTail b runLen tailBits tailLen := by
              exact fixedRunFastBitsEob_of_literal data i b j runLen tailBits tailLen
                hlt rfl rfl rfl rfl rfl h4
            have hout :
                fixedRunFastOut data i out =
                  fixedRunFastOut data j (pushRepeat out b runLen) := by
              exact fixedRunFastOut_of_literal data i out b j runLen hlt rfl rfl rfl h4
            have htail2 : 2 ≤ tailLen := by
              dsimp [tailLen]
              exact fixedRunFastBitsEob_len_ge_two data j
            have hbitNext : bwNext.bitPos < 8 := by
              simpa [bwNext] using fixedRunLiteralNextWriter_bitPos_lt bw b runLen hbit
            have hcurNext : bwNext.curClearAbove := by
              simpa [bwNext] using fixedRunLiteralNextWriter_curClearAbove bw b runLen hbit hcur
            have hstep :=
              decodeFixedBlockFuelFast_literalRepeatBitsTail_readerAt_writeBits_tail
                (fuel := fixedRunFastStepsEob data j) (bw := bw) (b := b)
                (n := runLen) (tailBits := tailBits) (tailLen := tailLen)
                (out := out) (htail2 := htail2) (hbit := hbit) (hcur := hcur)
            have hreaderRec :
                literalRepeatTailStartReader bw b runLen tailBits tailLen hbit =
                  fixedRunStartReader data j bwNext hbitNext := by
              simpa [fixedRunStartReader, bwNext, fixedRunLiteralNextWriter] using
                literalRepeatTailStartReader_eq_runtimeStartReader
                  bw b runLen tailBits tailLen hbit
            have hrec :
                decodeFixedBlockFuelFast (fixedRunFastStepsEob data j)
                  (literalRepeatTailStartReader bw b runLen tailBits tailLen hbit)
                  (pushRepeat out b runLen) =
                some (fixedRunAfterReader data j bwNext hbitNext,
                  fixedRunFastOut data j (pushRepeat out b runLen)) := by
              rw [hreaderRec]
              exact ih (data.size - j) hk' j bwNext (pushRepeat out b runLen)
                hbitNext hcurNext rfl
            have hwrite :
                BitWriter.writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2 =
                  BitWriter.writeBits bwNext tailBits tailLen := by
              simpa [hbits, bwNext, fixedRunLiteralNextWriter] using
                (writeBits_literalRepeatBitsTail
                  (bw := bw) (b := b) (n := runLen)
                  (tailBits := tailBits) (tailLen := tailLen))
            have hafter :
                fixedRunAfterReader data j bwNext hbitNext =
                  fixedRunAfterReader data i bw hbit := by
              simpa [tailBits, tailLen] using
                fixedRunAfterReader_eq_of_write_eq
                  (data := data) (i := i) (j := j)
                  (bw := bw) (bw' := bwNext)
                  (hbit := hbit) (hbit' := hbitNext) hwrite
            calc
              decodeFixedBlockFuelFast (fixedRunFastStepsEob data i)
                  (fixedRunStartReader data i bw hbit) out
                  =
                decodeFixedBlockFuelFast (fixedRunFastStepsEob data j)
                  (literalRepeatTailStartReader bw b runLen tailBits tailLen hbit)
                  (pushRepeat out b runLen) := by
                    simpa [fixedRunStartReader, hsteps, hbits,
                      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
              _ =
                some (fixedRunAfterReader data j bwNext hbitNext,
                  fixedRunFastOut data j (pushRepeat out b runLen)) := hrec
              _ =
                some (fixedRunAfterReader data i bw hbit, fixedRunFastOut data i out) := by
                  exact some_fixedRunState_eq_of_eqs
                    (data := data) (i := i) (j := j)
                    (bw := bw) (bw' := bwNext)
                    (hbit := hbit) (hbit' := hbitNext)
                    (out := out) (out' := pushRepeat out b runLen)
                    hafter hout
        · have hbase :=
            decodeFixedBlockFuelFast_step_eob_eobNoTail
              (fuel := 0) (bw := bw) (out := out) (hbit := hbit) (hcur := hcur)
          simpa [fixedRunStartReader, fixedRunAfterReader, fixedRunFastBitsEob, fixedRunFastStepsEob,
            fixedRunFastOut, hlt, flushReader, eobNoTailWriter, eobNoTailStartReader,
            eobNoTailAfterReader] using hbase
  exact hk (data.size - i) i bw out hbit hcur rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFast_fixedRunFastBitsEob_readerAt_writeBits
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedBlockFast (fixedRunStartReader data i bw hbit) out =
      some (fixedRunAfterReader data i bw hbit, fixedRunFastOut data i out) := by
  let br0 := fixedRunStartReader data i bw hbit
  have hstepsBits : fixedRunFastStepsEob data i ≤ (fixedRunFastBitsEob data i).2 := by
    exact fixedRunFastStepsEob_le_fixedRunFastBitsEob_len data i
  have hbitsLe : (fixedRunFastBitsEob data i).2 ≤ br0.data.size * 8 := by
    let bwAll := BitWriter.writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2
    have hbitAll : bwAll.bitPos < 8 := by
      dsimp [bwAll]
      exact bitPos_lt_8_writeBits bw (fixedRunFastBitsEob data i).1 (fixedRunFastBitsEob data i).2 hbit
    have hcount : (fixedRunFastBitsEob data i).2 ≤ bwAll.bitCount := by
      dsimp [bwAll]
      rw [bitCount_writeBits]
      exact Nat.le_add_left (fixedRunFastBitsEob data i).2 bw.bitCount
    have hflush : bwAll.bitCount ≤ bwAll.flush.size * 8 := by
      exact flush_size_mul_ge_bitCount (bw := bwAll) hbitAll
    simpa [br0, bwAll, fixedRunStartReader] using le_trans hcount hflush
  have hstepsLe : fixedRunFastStepsEob data i ≤ br0.data.size * 8 + 1 := by
    exact le_trans hstepsBits (le_trans hbitsLe (Nat.le_add_right _ _))
  let fuel := br0.data.size * 8 + 1 - fixedRunFastStepsEob data i
  have hfuel : fuel + fixedRunFastStepsEob data i = br0.data.size * 8 + 1 := by
    dsimp [fuel]
    exact Nat.sub_add_cancel hstepsLe
  have hfuel' : fixedRunFastStepsEob data i + fuel = br0.data.size * 8 + 1 := by
    simpa [Nat.add_comm] using hfuel
  have hexact :=
    decodeFixedBlockFuelFast_fixedRunFastBitsEob_exact
      (data := data) (i := i) (bw := bw) (out := out) (hbit := hbit) (hcur := hcur)
  have hdecode' :
      decodeFixedBlockFuelFast (br0.data.size * 8 + 1) br0 out =
        some (fixedRunAfterReader data i bw hbit, fixedRunFastOut data i out) := by
    have hplus :=
      decodeFixedBlockFuelFast_add_of_some
        (fuel := fixedRunFastStepsEob data i) (extra := fuel) (br := br0) (out := out)
        (res := (fixedRunAfterReader data i bw hbit, fixedRunFastOut data i out))
        (by simpa using hexact)
    rw [hfuel'] at hplus
    simpa using hplus
  simpa [decodeFixedBlockFast, br0, fixedRunStartReader] using hdecode'

end Lemmas

end Bitmaps
