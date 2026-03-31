import Bitmap.Lemmas.Png.EncodeDecodeBase
import Bitmap.Lemmas.Png.FixedBlockBase
import Bitmap.Lemmas.Png.FixedBlockProofsCommon
import Bitmap.Lemmas.Png.FixedBlockProofsScanDecode

universe u

namespace Bitmaps

namespace Lemmas

open Png
attribute [local simp] Png.byteArray_get_proof_irrel

lemma quadTailEqbFast_eq_quadTailEqb
    (data : Array UInt8) (i : Nat) (b : UInt8) (h3 : i + 3 < data.size) :
    quadTailEqbFast data i b h3 = quadTailEqb data i b h3 := by
  unfold quadTailEqbFast quadTailEqb
  rfl

lemma one_le_fixedLitLenCode_len_u8 (b : UInt8) :
    1 ≤ (fixedLitLenCode b.toNat).2 := by
  exact fixedLitLenCode_len_pos b.toNat (lt_trans (UInt8.toNat_lt b) (by decide))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma deflateFixedQuadAuxFast_writeBits (data : Array UInt8) (i : Nat) (bw : BitWriter) :
    let bitsLen := fixedQuadBitsEob data i
    let bw1 := deflateFixedQuadAuxFast data i bw
    let eob := fixedLitLenCode 256
    BitWriter.writeBits bw bitsLen.1 bitsLen.2 =
      BitWriter.writeBits bw1 (reverseBits eob.1 eob.2) eob.2 := by
  classical
  have hk :
      ∀ k, ∀ i bw, data.size - i = k →
        let bitsLen := fixedQuadBitsEob data i
        let bw1 := deflateFixedQuadAuxFast data i bw
        let eob := fixedLitLenCode 256
        BitWriter.writeBits bw bitsLen.1 bitsLen.2 =
          BitWriter.writeBits bw1 (reverseBits eob.1 eob.2) eob.2 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro i bw hk
        by_cases hlt : i < data.size
        · let b := data[i]
          by_cases h3 : i + 3 < data.size
          · by_cases hq : quadTailEqb data i b h3 = true
            · let tailBits := (fixedQuadBitsEob data (i + 4)).1
              let tailLen := (fixedQuadBitsEob data (i + 4)).2
              have hk' : data.size - (i + 4) < k := by
                have hlt' : data.size - (i + 4) < data.size - i := by omega
                simpa [hk] using hlt'
              have hih :=
                ih (data.size - (i + 4)) hk' (i := i + 4)
                  (bw := (BitWriter.writeFixedLiteralFast bw b).writeFixedMatchDist1Fast 3) rfl
              have hbits :
                  fixedQuadBitsEob data i = dist1RunBitsTail b 3 tailBits tailLen := by
                simpa [b, tailBits, tailLen] using
                  (fixedQuadBitsEob_of_quad (data := data) (i := i) (h := hlt) (h3 := h3)
                    (hq := by simpa [quadTailEqbFast_eq_quadTailEqb] using hq))
              have hbw1 :
                  deflateFixedQuadAuxFast data i bw =
                    deflateFixedQuadAuxFast data (i + 4)
                      ((BitWriter.writeFixedLiteralFast bw b).writeFixedMatchDist1Fast 3) := by
                rw [deflateFixedQuadAuxFast.eq_1]
                simp [hlt, b, h3, hq, quadTailEqbFast_eq_quadTailEqb]
              calc
                BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2
                    = BitWriter.writeBits ((BitWriter.writeFixedLiteralFast bw b).writeFixedMatchDist1Fast 3)
                        tailBits tailLen := by
                          simpa [hbits, tailBits, tailLen] using
                            (writeBits_dist1RunBitsTail_three (bw := bw) (b := b)
                              (tailBits := tailBits) (tailLen := tailLen))
                _ = BitWriter.writeBits
                      (deflateFixedQuadAuxFast data (i + 4)
                        ((BitWriter.writeFixedLiteralFast bw b).writeFixedMatchDist1Fast 3))
                      (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
                      (fixedLitLenCode 256).2 := by
                        simpa [tailBits, tailLen] using hih
                _ = BitWriter.writeBits (deflateFixedQuadAuxFast data i bw)
                      (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
                      (fixedLitLenCode 256).2 := by
                        simp [hbw1]
            · let tailBits := (fixedQuadBitsEob data (i + 1)).1
              let tailLen := (fixedQuadBitsEob data (i + 1)).2
              have hk' : data.size - (i + 1) < k := by
                have hlt' : data.size - (i + 1) < data.size - i := by
                  exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt
                    (Nat.lt_succ_self i)
                simpa [hk] using hlt'
              have hih :=
                ih (data.size - (i + 1)) hk' (i := i + 1)
                  (bw := BitWriter.writeFixedLiteralFast bw b) rfl
              have hbits :
                  fixedQuadBitsEob data i = literalRepeatBitsTail b 1 tailBits tailLen := by
                simpa [b, tailBits, tailLen] using
                  (fixedQuadBitsEob_of_lit_hqFalse (data := data) (i := i) (h := hlt) (h3 := h3)
                    (hq := by simpa [quadTailEqbFast_eq_quadTailEqb] using hq))
              have hbw1 :
                  deflateFixedQuadAuxFast data i bw =
                    deflateFixedQuadAuxFast data (i + 1) (BitWriter.writeFixedLiteralFast bw b) := by
                rw [deflateFixedQuadAuxFast.eq_1]
                simp [hlt, b, h3, hq, quadTailEqbFast_eq_quadTailEqb]
              calc
                BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2
                    = BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen := by
                        simpa [hbits, tailBits, tailLen] using
                          (writeBits_literalRepeatBitsTail_one (bw := bw) (b := b)
                            (tailBits := tailBits) (tailLen := tailLen))
                _ = BitWriter.writeBits
                      (deflateFixedQuadAuxFast data (i + 1) (BitWriter.writeFixedLiteralFast bw b))
                      (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
                      (fixedLitLenCode 256).2 := by
                        simpa [tailBits, tailLen] using hih
                _ = BitWriter.writeBits (deflateFixedQuadAuxFast data i bw)
                      (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
                      (fixedLitLenCode 256).2 := by
                        simp [hbw1]
          · let tailBits := (fixedQuadBitsEob data (i + 1)).1
            let tailLen := (fixedQuadBitsEob data (i + 1)).2
            have hk' : data.size - (i + 1) < k := by
              have hlt' : data.size - (i + 1) < data.size - i := by
                exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt
                  (Nat.lt_succ_self i)
              simpa [hk] using hlt'
            have hih :=
              ih (data.size - (i + 1)) hk' (i := i + 1)
                (bw := BitWriter.writeFixedLiteralFast bw b) rfl
            have hbits :
                fixedQuadBitsEob data i = literalRepeatBitsTail b 1 tailBits tailLen := by
              simpa [b, tailBits, tailLen] using
                (fixedQuadBitsEob_of_lit_noh3 (data := data) (i := i) (h := hlt) (h3 := h3))
            have hbw1 :
                deflateFixedQuadAuxFast data i bw =
                  deflateFixedQuadAuxFast data (i + 1) (BitWriter.writeFixedLiteralFast bw b) := by
              rw [deflateFixedQuadAuxFast.eq_1]
              simp [hlt, b, h3]
            calc
              BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2
                  = BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen := by
                      simpa [hbits, tailBits, tailLen] using
                        (writeBits_literalRepeatBitsTail_one (bw := bw) (b := b)
                          (tailBits := tailBits) (tailLen := tailLen))
              _ = BitWriter.writeBits
                    (deflateFixedQuadAuxFast data (i + 1) (BitWriter.writeFixedLiteralFast bw b))
                    (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
                    (fixedLitLenCode 256).2 := by
                      simpa [tailBits, tailLen] using hih
              _ = BitWriter.writeBits (deflateFixedQuadAuxFast data i bw)
                    (reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
                    (fixedLitLenCode 256).2 := by
                      simp [hbw1]
        · have hle : data.size ≤ i := Nat.le_of_not_gt hlt
          simp [fixedQuadBitsEob_unfold, deflateFixedQuadAuxFast, hlt, fixedLitLenCode]
  exact hk (data.size - i) i bw rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma deflateFixedQuadFast_eq_writeBits (raw : ByteArray) :
    let bw0 := BitWriter.empty
    let bw1 := bw0.writeBits 1 1
    let bw2 := bw1.writeBits 1 2
    let bitsLen := fixedQuadBitsEob raw.data 0
    deflateFixedQuadFast raw = (BitWriter.writeBits bw2 bitsLen.1 bitsLen.2).flush := by
  unfold deflateFixedQuadFast
  have hbits :=
    deflateFixedQuadAuxFast_writeBits raw.data 0
      (BitWriter.writeBits (BitWriter.writeBits BitWriter.empty 1 1) 1 2)
  simp at hbits
  simpa using (congrArg BitWriter.flush hbits).symm

lemma fixedQuadStepsEob_le_fixedQuadBitsEob_len
    (data : Array UInt8) (i : Nat) :
    fixedQuadStepsEob data i ≤ (fixedQuadBitsEob data i).2 := by
  classical
  by_cases hlt : i < data.size
  ·
    let b := data[i]
    by_cases h3 : i + 3 < data.size
    · dsimp [b]
      by_cases hq : quadTailEqb data i b h3 = true
      · have htail : fixedQuadStepsEob data (i + 4) ≤ (fixedQuadBitsEob data (i + 4)).2 := by
          exact fixedQuadStepsEob_le_fixedQuadBitsEob_len data (i + 4)
        have hsteps :
            fixedQuadStepsEob data i = 2 + fixedQuadStepsEob data (i + 4) := by
          have hsteps0 :=
            fixedQuadStepsEob_of_quad (data := data) (i := i) (h := hlt) (h3 := h3)
              (hq := by simpa [b] using hq)
          simpa [dist1RunSteps_three, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsteps0
        have hbits :
            fixedQuadBitsEob data i =
              dist1RunBitsTail b 3 (fixedQuadBitsEob data (i + 4)).1 (fixedQuadBitsEob data (i + 4)).2 := by
          simpa [b] using
            (fixedQuadBitsEob_of_quad (data := data) (i := i) (h := hlt) (h3 := h3)
              (hq := by simpa [b] using hq))
        have hlen :
            2 + (fixedQuadBitsEob data (i + 4)).2 ≤
              (dist1RunBitsTail b 3 (fixedQuadBitsEob data (i + 4)).1
                (fixedQuadBitsEob data (i + 4)).2).2 := by
          simp [dist1RunBitsTail_three, dist1ChunkLoopBitsTail_three, fixedLenMatchInfo_three]
          omega
        simpa [hsteps, hbits] using le_trans (Nat.add_le_add_left htail 2) hlen
      · have htail : fixedQuadStepsEob data (i + 1) ≤ (fixedQuadBitsEob data (i + 1)).2 := by
          exact fixedQuadStepsEob_le_fixedQuadBitsEob_len data (i + 1)
        have hsteps :
            fixedQuadStepsEob data i = 1 + fixedQuadStepsEob data (i + 1) := by
          simpa [b] using
            (fixedQuadStepsEob_of_lit_hqFalse (data := data) (i := i) (h := hlt) (h3 := h3)
              (hq := by simpa [b] using hq))
        have hbits :
            fixedQuadBitsEob data i =
              literalRepeatBitsTail b 1 (fixedQuadBitsEob data (i + 1)).1 (fixedQuadBitsEob data (i + 1)).2 := by
          simpa [b] using
            (fixedQuadBitsEob_of_lit_hqFalse (data := data) (i := i) (h := hlt) (h3 := h3)
              (hq := by simpa [quadTailEqbFast_eq_quadTailEqb] using hq))
        have hlen :
            1 + (fixedQuadBitsEob data (i + 1)).2 ≤
              (literalRepeatBitsTail b 1 (fixedQuadBitsEob data (i + 1)).1
                (fixedQuadBitsEob data (i + 1)).2).2 := by
          have hcode : 1 ≤ (fixedLitLenCode b.toNat).2 := one_le_fixedLitLenCode_len_u8 b
          simp [literalRepeatBitsTail_succ, literalRepeatBitsTail_zero]
          omega
        simpa [hsteps, hbits] using le_trans (Nat.add_le_add_left htail 1) hlen
    · dsimp [b]
      have htail : fixedQuadStepsEob data (i + 1) ≤ (fixedQuadBitsEob data (i + 1)).2 := by
        exact fixedQuadStepsEob_le_fixedQuadBitsEob_len data (i + 1)
      have hsteps :
          fixedQuadStepsEob data i = 1 + fixedQuadStepsEob data (i + 1) := by
        simpa [b] using
          (fixedQuadStepsEob_of_lit_noh3 (data := data) (i := i) (h := hlt) (h3 := h3))
      have hbits :
          fixedQuadBitsEob data i =
            literalRepeatBitsTail b 1 (fixedQuadBitsEob data (i + 1)).1 (fixedQuadBitsEob data (i + 1)).2 := by
        simpa [b] using
          (fixedQuadBitsEob_of_lit_noh3 (data := data) (i := i) (h := hlt) (h3 := h3))
      have hlen :
          1 + (fixedQuadBitsEob data (i + 1)).2 ≤
            (literalRepeatBitsTail b 1 (fixedQuadBitsEob data (i + 1)).1
              (fixedQuadBitsEob data (i + 1)).2).2 := by
        have hcode : 1 ≤ (fixedLitLenCode b.toNat).2 := one_le_fixedLitLenCode_len_u8 b
        simp [literalRepeatBitsTail_succ, literalRepeatBitsTail_zero]
        omega
      simpa [hsteps, hbits] using le_trans (Nat.add_le_add_left htail 1) hlen
  · have hsteps : fixedQuadStepsEob data i = 1 := by
        simp [fixedQuadStepsEob_unfold, hlt]
    have hbits : (fixedQuadBitsEob data i).2 = (fixedLitLenCode 256).2 := by
        simp [fixedQuadBitsEob_unfold, hlt]
    simpa [hsteps, hbits] using (show 1 ≤ (fixedLitLenCode 256).2 by decide)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFast_fixedQuadBitsEob_readerAt_writeBits
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedBlockFast
      (BitWriter.readerAt bw
        (BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2).flush
        (flush_size_writeBits_le bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2) hbit) out =
      some (flushReader
        (BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2)
        (bitPos_lt_8_writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2 hbit),
      fixedQuadOut data i out) := by
  let br0 := Png.fixedQuadStartReader data i bw hbit
  have hstepsBits : fixedQuadStepsEob data i ≤ (fixedQuadBitsEob data i).2 := by
    exact fixedQuadStepsEob_le_fixedQuadBitsEob_len data i
  have hbitsLe : (fixedQuadBitsEob data i).2 ≤ br0.data.size * 8 := by
    let bwAll := BitWriter.writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2
    have hbitAll : bwAll.bitPos < 8 := by
      dsimp [bwAll]
      exact bitPos_lt_8_writeBits bw (fixedQuadBitsEob data i).1 (fixedQuadBitsEob data i).2 hbit
    have hcount :
        (fixedQuadBitsEob data i).2 ≤ bwAll.bitCount := by
      dsimp [bwAll]
      rw [bitCount_writeBits]
      exact Nat.le_add_left (fixedQuadBitsEob data i).2 bw.bitCount
    have hflush : bwAll.bitCount ≤ bwAll.flush.size * 8 := by
      exact flush_size_mul_ge_bitCount (bw := bwAll) hbitAll
    simpa [br0, bwAll, Png.fixedQuadStartReader] using le_trans hcount hflush
  have hstepsLe : fixedQuadStepsEob data i ≤ br0.data.size * 8 + 1 := by
    exact le_trans hstepsBits (le_trans hbitsLe (Nat.le_add_right _ _))
  let fuel := br0.data.size * 8 + 1 - fixedQuadStepsEob data i
  have hfuel : fuel + fixedQuadStepsEob data i = br0.data.size * 8 + 1 := by
    dsimp [fuel]
    exact Nat.sub_add_cancel hstepsLe
  have hfuel' : fixedQuadStepsEob data i + fuel = br0.data.size * 8 + 1 := by
    simpa [Nat.add_comm] using hfuel
  rcases
    (Png.decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_exists
      (data := data) (i := i) (bw := bw) (out := out) (hbit := hbit) (hcur := hcur))
    with ⟨brAfter, hexists⟩
  have hreader :
      brAfter =
        Png.fixedQuadAfterReader data i bw hbit := by
    exact
      Png.decodeFixedBlockFuelFast_fixedQuadBitsEob_readerAt_writeBits_reader_eq
        (data := data) (i := i) (bw := bw) (out := out) (hbit := hbit) (hcur := hcur)
        (brAfter := brAfter) (by simpa [br0] using hexists)
  have hexact :
      decodeFixedBlockFuelFast (fixedQuadStepsEob data i) br0 out =
        some
          (Png.fixedQuadAfterReader data i bw hbit,
          fixedQuadOut data i out) := by
    simpa [br0, hreader] using hexists
  have hdecode' :
      decodeFixedBlockFuelFast (br0.data.size * 8 + 1) br0 out =
        some
          (Png.fixedQuadAfterReader data i bw hbit,
          fixedQuadOut data i out) := by
    have hplus :=
      decodeFixedBlockFuelFast_add_of_some
        (fuel := fixedQuadStepsEob data i) (extra := fuel) (br := br0) (out := out)
        (res := (Png.fixedQuadAfterReader data i bw hbit,
          fixedQuadOut data i out)) (by
            simpa using hexact)
    rw [hfuel'] at hplus
    simpa using hplus
  simpa [decodeFixedBlockFast, br0, Png.fixedQuadStartReader, Png.fixedQuadAfterReader, Png.flushReader] using hdecode'

set_option maxHeartbeats 6000000 in
-- Zlib decompression of fixed-compression output yields the original bytes.
lemma zlibDecompress_zlibCompressFixed (raw : ByteArray)
    (hsize : 2 ≤ (zlibCompressFixed raw).size) :
    zlibDecompress (zlibCompressFixed raw) hsize = some raw := by
  classical
  let bytes := zlibCompressFixed raw
  have hmin : 6 ≤ bytes.size := zlibCompressFixed_size_ge raw
  have h0 : 0 < bytes.size := lt_of_lt_of_le (by decide : 0 < 6) hmin
  have h1 : 1 < bytes.size := lt_of_lt_of_le (by decide : 1 < 6) hmin
  have h0' : 0 < bytes.size := h0
  have h1' : 1 < bytes.size := h1
  have hcmf' : bytes[0]'h0' = u8 0x78 := (zlibCompressFixed_cmf_flg raw).1
  have hflg' : bytes[1]'h1' = u8 0x01 := (zlibCompressFixed_cmf_flg raw).2
  have hcmf : bytes.get 0 h0 = u8 0x78 := by
    have htmp : bytes.get 0 h0' = u8 0x78 := by
      simpa [byteArray_get_eq_getElem] using hcmf'
    simpa using htmp
  have hflg : bytes.get 1 h1 = u8 0x01 := by
    have htmp : bytes.get 1 h1' = u8 0x01 := by
      simpa [byteArray_get_eq_getElem] using hflg'
    simpa using htmp
  have hdeflated : bytes.extract 2 (bytes.size - 4) = deflateFixed raw := by
    simpa [bytes] using zlibCompressFixed_extract_deflated raw
  have hAdlerPos : bytes.size - 4 + 3 < bytes.size := by omega
  have hadler : readU32BE bytes (bytes.size - 4) hAdlerPos = (adler32 raw).toNat := by
    have hextract :
        bytes.extract (bytes.size - 4) (bytes.size - 4 + 4) =
          u32be (adler32 raw).toNat := by
      simpa [bytes] using zlibCompressFixed_extract_adler raw
    have hlt : (adler32 raw).toNat < 2 ^ 32 := by
      simpa using (UInt32.toNat_lt (adler32 raw))
    exact readU32BE_of_extract_eq (bytes := bytes) (pos := bytes.size - 4)
      (n := (adler32 raw).toNat) (h := hAdlerPos) hextract hlt
  have hmod : ((u8 0x78).toNat <<< 8 + (u8 0x01).toNat) % 31 = 0 := by
    decide
  have hbtype : (u8 0x78 &&& (0x0F : UInt8)) = 8 := by
    decide
  have hflg0 : (u8 0x01 &&& (0x20 : UInt8)) = 0 := by
    decide
  -- prepare the fixed block decoder
  let hdr0 := BitWriter.empty
  let hdrBfinal := hdr0.writeBits 1 1
  let hdrHeader := hdrBfinal.writeBits 1 2
  let payloadBits := fixedQuadBitsEob raw.data 0
  have hcur0 : hdr0.curClearAbove := curClearAbove_empty
  have hcur1 : hdrBfinal.curClearAbove := curClearAbove_writeBits hdr0 1 1 (by decide) hcur0
  have hcur2 : hdrHeader.curClearAbove := curClearAbove_writeBits hdrBfinal 1 2 (by decide) hcur1
  have hbitHdr : hdrHeader.bitPos < 8 := by
    exact bitPos_lt_8_writeBits hdrBfinal 1 2 (bitPos_lt_8_writeBits hdr0 1 1 (by decide))
  have hdeflateBits :
      deflateFixed raw = (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush := by
    calc
      deflateFixed raw = deflateFixedQuadFast raw := deflateFixed_eq_quadFast raw
      _ = (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush := by
            simpa [payloadBits] using deflateFixedQuadFast_eq_writeBits raw
  -- Collapse the header bits into one write.
  let streamBits := 3 ||| (payloadBits.1 <<< 3)
  let streamLen := 3 + payloadBits.2
  let streamWriter := BitWriter.writeBits hdr0 streamBits streamLen
  have hbw2 : hdrHeader = BitWriter.writeBits hdr0 3 3 := by
    have hbits : (1 : Nat) < 2 ^ 1 := by decide
    have hconcat := writeBits_concat hdr0 1 1 1 2 hbits
    have h' : BitWriter.writeBits hdr0 3 3 = hdrHeader := by
      simpa [hdrBfinal, hdrHeader] using hconcat
    simpa using h'.symm
  have hdeflateTotal : deflateFixed raw = streamWriter.flush := by
    have hbits : 3 < 2 ^ 3 := by decide
    have hconcat := writeBits_concat hdr0 3 payloadBits.1 3 payloadBits.2 hbits
    calc
      deflateFixed raw = (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush := hdeflateBits
      _ = (BitWriter.writeBits (BitWriter.writeBits hdr0 3 3) payloadBits.1 payloadBits.2).flush := by
            simp [hbw2]
      _ = streamWriter.flush := by
            simpa [streamWriter, streamBits, streamLen] using (congrArg BitWriter.flush hconcat).symm
  have hmod3 : streamBits % 2 ^ 3 = 3 := by
    have h := mod_two_pow_or_shift (a := 3) (b := payloadBits.1) (k := 3) (len := 3) (by decide)
    simpa [streamBits] using h
  have hprefix : BitWriter.writeBits hdr0 streamBits 3 = hdrHeader := by
    have hbw2' : BitWriter.writeBits hdr0 3 3 = hdrHeader := by
      simpa using hbw2.symm
    calc
      BitWriter.writeBits hdr0 streamBits 3 =
          BitWriter.writeBits hdr0 (streamBits % 2 ^ 3) 3 := by
            simpa using (writeBits_mod hdr0 streamBits 3)
      _ = BitWriter.writeBits hdr0 3 3 := by
            simp [hmod3]
      _ = hdrHeader := hbw2'
  -- Reader at the start of the deflated stream.
  let streamReader0 : BitReader := {
    data := streamWriter.flush
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide
  }
  have hbw0 : hdr0.bitPos = 0 := rfl
  have hbw0out : hdr0.out.size = 0 := by
    simp [hdr0, BitWriter.empty]
  have hbr0 :
      streamReader0 = BitWriter.readerAt hdr0 streamWriter.flush
        (flush_size_writeBits_le hdr0 streamBits streamLen) (by decide) := by
    apply BitReader.ext <;> simp [streamReader0, BitWriter.readerAt, hdr0, hbw0, hbw0out]
  let streamReaderHeader := BitWriter.readerAt hdrHeader streamWriter.flush
      (by
        simpa [hprefix] using
          (flush_size_writeBits_prefix (bw := hdr0) (bits := streamBits) (k := 3)
            (len := streamLen) (hk := by omega)))
      (by
        simpa [hprefix] using
          (bitPos_lt_8_writeBits hdr0 streamBits 3 (by decide)))
  let payloadReaderStart := BitWriter.readerAt hdrHeader
      (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush
      (flush_size_writeBits_le hdrHeader payloadBits.1 payloadBits.2)
      hbitHdr
  have hpayloadData :
      (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush = streamWriter.flush := by
    exact hdeflateBits.symm.trans hdeflateTotal
  have hpayloadStart : streamReaderHeader = payloadReaderStart := by
    apply BitReader.ext <;> simp [streamReaderHeader, payloadReaderStart, hpayloadData]
  have hread0_at :
      (BitWriter.readerAt hdr0 streamWriter.flush
        (flush_size_writeBits_le hdr0 streamBits streamLen) (by decide)).bitIndex + 3 ≤
        (BitWriter.readerAt hdr0 streamWriter.flush
          (flush_size_writeBits_le hdr0 streamBits streamLen) (by decide)).data.size * 8 := by
    simpa using
      (readerAt_writeBits_bound (bw := hdr0) (bits := streamBits) (len := streamLen) (k := 3)
        (hk := by omega) (hbit := by decide))
  have hread0 : streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := by
    simpa [hbr0] using hread0_at
  have hread3 : streamReader0.readBits 3 hread0 = (3, streamReaderHeader) := by
    have h' :=
      (readBits_readerAt_writeBits_prefix (bw := hdr0) (bits := streamBits) (len := streamLen)
        (k := 3) (hk := by omega) (hbit := by decide) (hcur := curClearAbove_empty)
        (hread := hread0_at))
    dsimp at h'
    have h'br : streamReader0.readBits 3 hread0_at = (3, streamReaderHeader) := by
      -- rewrite with the collapsed header bits and prefix reader
      simpa [hbr0, hmod3, hprefix, streamReaderHeader, hdr0, hbw0] using h'
    have hirrel : streamReader0.readBits 3 hread0 = streamReader0.readBits 3 hread0_at :=
      readBits_proof_irrel (br := streamReader0) (n := 3) hread0 hread0_at
    exact hirrel.trans h'br
  have hrawOut : fixedQuadOut raw.data 0 ByteArray.empty = raw := by
    simpa using fixedQuadOut_empty raw.data
  let streamReaderFinal := BitWriter.readerAt
    (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2)
    (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush
    (by rfl)
    (bitPos_lt_8_writeBits hdrHeader payloadBits.1 payloadBits.2 hbitHdr)
  have hdecodeFast :
      decodeFixedBlockFast payloadReaderStart ByteArray.empty =
        some (streamReaderFinal, raw) := by
    simpa [payloadReaderStart, payloadBits, streamReaderFinal, decodeFixedBlock, hrawOut] using
      (decodeFixedBlockFast_fixedQuadBitsEob_readerAt_writeBits
        (data := raw.data) (i := 0) (bw := hdrHeader) (out := ByteArray.empty)
        (hbit := hbitHdr) (hcur := hcur2))
  -- Evaluate the block decoder once.
  have hloop :
      zlibDecompressLoop streamReader0 ByteArray.empty =
        some (streamReaderFinal, raw) := by
    have hdecode' : decodeFixedBlock streamReaderHeader ByteArray.empty =
        some (streamReaderFinal, raw) := by
      rw [hpayloadStart]
      simpa [decodeFixedBlock, hrawOut] using hdecodeFast
    -- Evaluate the loop body (bfinal = 1, btype = 1).
    have hbfinal : (3 % 2) = 1 := by decide
    have hbtype' : ((3 >>> 1) % 4) = 1 := by decide
    have hcond : streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := hread0
    have hread3' : streamReader0.readBits 3 hcond = (3, streamReaderHeader) := by
      simpa using hread3
    simp [zlibDecompressLoop, zlibDecompressLoopFuel, hcond, hread3', hdecode', hbfinal]
  -- Evaluate the decompressor on the fixed-compression stream.
  unfold zlibDecompress
  -- simplify header checks and the deflated slice
  simp [bytes, hcmf, hflg, hmod, hbtype, hflg0, hdeflated, hdeflateTotal, streamWriter]
  -- replace the loop with its computed result
  rw [hloop]
  -- compute the Adler position and value
  have hAlign : streamReaderFinal.alignByte.bytePos = streamWriter.flush.size := by
    have hpayloadSize :
        (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush.size =
          streamWriter.flush.size := by
      simp [hpayloadData]
    calc
      streamReaderFinal.alignByte.bytePos =
          (BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2).flush.size := by
            simpa [streamReaderFinal] using
              (readerAt_alignByte_bytePos_eq_flush
                (bw := BitWriter.writeBits hdrHeader payloadBits.1 payloadBits.2)
                (hbit := bitPos_lt_8_writeBits hdrHeader payloadBits.1 payloadBits.2 hbitHdr))
      _ = streamWriter.flush.size := hpayloadSize
  have hsize : bytes.size = streamWriter.flush.size + 6 := by
    -- size = deflate + header + adler
    have hsz := zlibCompressFixed_size raw
    simpa [bytes, hdeflateTotal] using hsz
  have hposEq : streamReaderFinal.alignByte.bytePos + 2 = bytes.size - 4 := by
    -- bytes.size = streamWriter.flush.size + 6
    have : streamWriter.flush.size + 2 = (streamWriter.flush.size + 6) - 4 := by omega
    simpa [hAlign, hsize, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hAdlerPos' : streamReaderFinal.alignByte.bytePos + 2 + 3 < bytes.size := by
    -- rewrite to the canonical Adler position
    simpa [hposEq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAdlerPos
  have hread : readU32BE bytes (streamReaderFinal.alignByte.bytePos + 2) hAdlerPos' = (adler32 raw).toNat := by
    simpa [hposEq, readU32BE_proof_irrel] using hadler
  -- close the final Adler check
  simp [hAdlerPos', hread, bytes]

-- Zlib decompression of dynamic-compression output yields the original bytes.
lemma zlibDecompress_zlibCompressDynamic (raw : ByteArray)
    (hsize : 2 ≤ (zlibCompressDynamic raw).size) :
    zlibDecompress (zlibCompressDynamic raw) hsize = some raw := by
  have hz : zlibCompressDynamic raw = zlibCompressFixed raw := by
    rfl
  have hsizeFixed : 2 ≤ (zlibCompressFixed raw).size := by
    simpa [hz] using hsize
  simpa [hz] using
    (zlibDecompress_zlibCompressFixed (raw := raw) (hsize := hsizeFixed))

end Lemmas

end Bitmaps
