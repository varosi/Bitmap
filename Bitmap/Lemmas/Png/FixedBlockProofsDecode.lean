import Bitmap.Lemmas.Png.FixedBlockProofsDecodeEob

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

lemma decodeFixedBlockFuelFast_step_literal_of_decodes
    (fuel : Nat) (br br' : BitReader) (out : ByteArray) (sym : Nat)
    (hdecodeSym : decodeFixedLiteralSymFast9 br = some (sym, br'))
    (hlit : sym < 256) :
    decodeFixedBlockFuelFast (fuel + 1) br out =
      decodeFixedBlockFuelFast fuel br' (out.push (u8 sym)) := by
  rw [decodeFixedBlockFuelFast.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  let k : Nat → BitReader → Option (BitReader × ByteArray) := fun sym br' =>
    if sym < 256 then
      decodeFixedBlockFuelFast fuel br' (out.push (u8 sym))
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
          let (distSym, br''') ← decodeFixedDistanceSym br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeFixedBlockFuelFast fuel br'''' out'
            else
              none
          else
            none
      else
        none
    else
      none
  change (match (sym, br') with | (s, r) => k s r) = decodeFixedBlockFuelFast fuel br' (out.push (u8 sym))
  have hpair : (match (sym, br') with | (s, r) => k s r) = k sym br' := by
    simpa using (match_pair_eta (a := sym) (b := br') (k := k))
  rw [hpair]
  dsimp [k]
  rw [if_pos hlit]

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_eob_of_decodes
    (fuel : Nat) (br br' : BitReader) (out : ByteArray) (sym : Nat)
    (hdecodeSym : decodeFixedLiteralSymFast9 br = some (sym, br'))
    (hnotLit : ¬ sym < 256) (heob : (sym == 256) = true) :
    decodeFixedBlockFuelFast (fuel + 1) br out = some (br', out) := by
  rw [decodeFixedBlockFuelFast.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  let k : Nat → BitReader → Option (BitReader × ByteArray) := fun sym br' =>
    if sym < 256 then
      decodeFixedBlockFuelFast fuel br' (out.push (u8 sym))
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
          let (distSym, br''') ← decodeFixedDistanceSym br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeFixedBlockFuelFast fuel br'''' out'
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
  rw [if_neg hnotLit]
  rw [if_pos heob]

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_literal_readerAt_writeBits
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (out : ByteArray)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let sym := b.toNat
    let codeLen := fixedLitLenCode sym
    let bits := reverseBits codeLen.1 codeLen.2
    let bitsTot := bits ||| (tailBits <<< codeLen.2)
    let lenTot := codeLen.2 + tailLen
    let bwAll := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bwAll.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedBlockFuelFast (fuel + 1) br0 out =
      let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
      let br1 := BitWriter.readerAt bw1 bwAll.flush
        (by
          have hk : codeLen.2 ≤ lenTot := by omega
          simpa [bwAll, lenTot] using (flush_size_writeBits_prefix bw bitsTot codeLen.2 lenTot hk))
        (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit)
      decodeFixedBlockFuelFast fuel br1 (out.push b) := by
  let sym := b.toNat
  let codeLen := fixedLitLenCode sym
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (tailBits <<< codeLen.2)
  let lenTot := codeLen.2 + tailLen
  let bwAll := BitWriter.writeBits bw bitsTot lenTot
  let br0 := BitWriter.readerAt bw bwAll.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
  let br1 := BitWriter.readerAt bw1 bwAll.flush
    (by
      have hk : codeLen.2 ≤ lenTot := by omega
      simpa [bwAll, lenTot] using (flush_size_writeBits_prefix bw bitsTot codeLen.2 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit)
  have hsym : sym < 288 := by
    exact lt_trans (UInt8.toNat_lt b) (by decide)
  have hlit : sym < 256 := by
    simpa [sym] using (UInt8.toNat_lt b)
  have hdecodeSym0 :
      decodeFixedLiteralSymFast9 br0 = some (sym, br1) := by
    simpa [sym, codeLen, bits, bitsTot, lenTot, bwAll, br0, bw1, br1] using
      (decodeFixedLiteralSymFast9_readerAt_writeBits (bw := bw) (sym := sym)
        (restBits := tailBits) (restLen := tailLen)
        (hsym := hsym) (hrest2 := htail2) (hbit := hbit) (hcur := hcur))
  simpa [sym, codeLen, bits, bitsTot, lenTot, bwAll, br0, bw1, br1, u8] using
    (decodeFixedBlockFuelFast_step_literal_of_decodes
      (fuel := fuel) (br := br0) (br' := br1) (out := out) (sym := sym)
      (hdecodeSym := hdecodeSym0) (hlit := hlit))

lemma literalTailWriter_bitPos_lt
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (hbit : bw.bitPos < 8) :
    (literalTailWriter bw b tailBits tailLen).bitPos < 8 := by
  dsimp [literalTailWriter]
  exact bitPos_lt_8_writeBits _ _ _ hbit

lemma literalTailWriter_curClearAbove
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (literalTailWriter bw b tailBits tailLen).curClearAbove := by
  dsimp [literalTailWriter]
  exact curClearAbove_writeBits _ _ _ hbit hcur

def literalTailStartReader (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bwTail := literalTailWriter bw b tailBits tailLen
  BitWriter.readerAt bwTail (BitWriter.writeBits bwTail tailBits tailLen).flush
    (flush_size_writeBits_le bwTail tailBits tailLen)
    (literalTailWriter_bitPos_lt bw b tailBits tailLen hbit)

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_literal_readerAt_writeBits_tail
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) (out : ByteArray)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedBlockFuelFast (fuel + 1)
      (BitWriter.readerAt bw
        (BitWriter.writeBits bw (literalRepeatBitsTail b 1 tailBits tailLen).1
          (literalRepeatBitsTail b 1 tailBits tailLen).2).flush
        (flush_size_writeBits_le bw
          (literalRepeatBitsTail b 1 tailBits tailLen).1
          (literalRepeatBitsTail b 1 tailBits tailLen).2) hbit) out =
      decodeFixedBlockFuelFast fuel (literalTailStartReader bw b tailBits tailLen hbit) (out.push b) := by
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (tailBits <<< codeLen.2)
  let lenTot := codeLen.2 + tailLen
  have hstep :=
    decodeFixedBlockFuelFast_step_literal_readerAt_writeBits
      (fuel := fuel) (bw := bw) (b := b) (tailBits := tailBits) (tailLen := tailLen)
      (out := out) (htail2 := htail2) (hbit := hbit) (hcur := hcur)
  let bwAll := BitWriter.writeBits bw bitsTot lenTot
  let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
  let br1 := BitWriter.readerAt bw1 bwAll.flush
    (by
      have hk : codeLen.2 ≤ lenTot := by omega
      simpa [bwAll, lenTot] using (flush_size_writeBits_prefix bw bitsTot codeLen.2 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit)
  have hbitsLt : bits < 2 ^ codeLen.2 := by
    simpa [bits] using (reverseBits_lt codeLen.1 codeLen.2)
  have hconcat :
      BitWriter.writeBits bw bitsTot lenTot =
        BitWriter.writeBits (BitWriter.writeBits bw bitsTot codeLen.2) tailBits tailLen := by
    -- `bitsTot` and `bits` are equivalent for the first `codeLen` bits.
    have hmod : bitsTot % 2 ^ codeLen.2 = bits := by
      have hmod' : bitsTot % 2 ^ codeLen.2 = bits % 2 ^ codeLen.2 := by
        simpa [bitsTot] using
          (mod_two_pow_or_shift (a := bits) (b := tailBits) (k := codeLen.2) (len := codeLen.2)
            (hk := le_rfl))
      exact by simpa [Nat.mod_eq_of_lt hbitsLt] using hmod'
    have hwrite :
        BitWriter.writeBits bw bitsTot codeLen.2 = BitWriter.writeBits bw bits codeLen.2 := by
      calc
        BitWriter.writeBits bw bitsTot codeLen.2
            = BitWriter.writeBits bw (bitsTot % 2 ^ codeLen.2) codeLen.2 := by
                simpa using (writeBits_mod bw bitsTot codeLen.2)
        _ = BitWriter.writeBits bw bits codeLen.2 := by
              simp [hmod]
    have hcat := writeBits_concat bw bits tailBits codeLen.2 tailLen hbitsLt
    calc
      BitWriter.writeBits bw bitsTot lenTot
          = BitWriter.writeBits bw (bits ||| (tailBits <<< codeLen.2)) lenTot := by
              simp [bitsTot]
      _ = BitWriter.writeBits (BitWriter.writeBits bw bits codeLen.2) tailBits tailLen := by
              simpa [lenTot, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcat
      _ = BitWriter.writeBits (BitWriter.writeBits bw bitsTot codeLen.2) tailBits tailLen := by
              rw [hwrite]
  have hbr1 :
      br1 = literalTailStartReader bw b tailBits tailLen hbit := by
    apply BitReader.ext
    · change bwAll.flush = (BitWriter.writeBits (literalTailWriter bw b tailBits tailLen) tailBits tailLen).flush
      dsimp [literalTailStartReader, literalTailWriter, bwAll]
      simpa [bw1] using congrArg BitWriter.flush hconcat
    · change bw1.out.size = (literalTailWriter bw b tailBits tailLen).out.size
      dsimp [literalTailWriter, bw1]
    · change bw1.bitPos = (literalTailWriter bw b tailBits tailLen).bitPos
      dsimp [literalTailWriter, bw1]
  have hlitTail :
      literalRepeatBitsTail b 1 tailBits tailLen = (bitsTot, lenTot) := by
    simp [literalRepeatBitsTail, codeLen, bits, bitsTot, lenTot]
  have hstep' :
      decodeFixedBlockFuelFast (fuel + 1)
        (BitWriter.readerAt bw
          (BitWriter.writeBits bw (literalRepeatBitsTail b 1 tailBits tailLen).1
            (literalRepeatBitsTail b 1 tailBits tailLen).2).flush
          (flush_size_writeBits_le bw
            (literalRepeatBitsTail b 1 tailBits tailLen).1
            (literalRepeatBitsTail b 1 tailBits tailLen).2) hbit) out =
        decodeFixedBlockFuelFast fuel br1 (out.push b) := by
    simpa [hlitTail, bwAll, br1] using hstep
  simpa [hbr1] using hstep'

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_eob_readerAt_writeBits
    (fuel : Nat) (bw : BitWriter) (tailBits tailLen : Nat) (out : ByteArray)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let sym := 256
    let codeLen := fixedLitLenCode sym
    let bits := reverseBits codeLen.1 codeLen.2
    let bitsTot := bits ||| (tailBits <<< codeLen.2)
    let lenTot := codeLen.2 + tailLen
    let bwAll := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bwAll.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedBlockFuelFast (fuel + 1) br0 out =
      some (
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot codeLen.2) bwAll.flush
          (by
            have hk : codeLen.2 ≤ lenTot := by omega
            simpa [bwAll, lenTot] using (flush_size_writeBits_prefix bw bitsTot codeLen.2 lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit),
        out) := by
  let sym : Nat := 256
  let codeLen := fixedLitLenCode sym
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (tailBits <<< codeLen.2)
  let lenTot := codeLen.2 + tailLen
  let bwAll := BitWriter.writeBits bw bitsTot lenTot
  let br0 := BitWriter.readerAt bw bwAll.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br1 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot codeLen.2) bwAll.flush
    (by
      have hk : codeLen.2 ≤ lenTot := by omega
      simpa [bwAll, lenTot] using (flush_size_writeBits_prefix bw bitsTot codeLen.2 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit)
  have hsym : sym < 288 := by
    decide
  have hdecodeSym0 :
      decodeFixedLiteralSymFast9 br0 = some (sym, br1) := by
    simpa [sym, codeLen, bits, bitsTot, lenTot, bwAll, br0, br1] using
      (decodeFixedLiteralSymFast9_readerAt_writeBits (bw := bw) (sym := sym)
        (restBits := tailBits) (restLen := tailLen)
        (hsym := hsym) (hrest2 := htail2) (hbit := hbit) (hcur := hcur))
  have hnotLit : ¬ sym < 256 := by
    decide
  have heob : (sym == 256) = true := by
    simp [sym]
  simpa [sym, codeLen, bits, bitsTot, lenTot, bwAll, br0, br1] using
    (decodeFixedBlockFuelFast_step_eob_of_decodes
      (fuel := fuel) (br := br0) (br' := br1) (out := out) (sym := sym)
      (hdecodeSym := hdecodeSym0) (hnotLit := hnotLit) (heob := heob))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
set_option linter.constructorNameAsVariable false in
lemma decodeFixedLiteralSymFast9_eobNoTail_h9
    (bw : BitWriter) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    (h9 : (eobNoTailStartReader bw hbit).bitIndex + 9 ≤ (eobNoTailStartReader bw hbit).data.size * 8) :
    decodeFixedLiteralSymFast9 (eobNoTailStartReader bw hbit) =
      some (256, eobNoTailAfterReader bw hbit) := by
  let sym : Nat := 256
  let codeLen := fixedLitLenCode sym
  let bits := reverseBits codeLen.1 codeLen.2
  let lenTot := codeLen.2
  let bwAll := eobNoTailWriter bw
  let br0 := eobNoTailStartReader bw hbit
  let br1 := eobNoTailAfterReader bw hbit
  have h9' : br0.bitIndex + 9 ≤ br0.data.size * 8 := by
    simpa [br0] using h9
  have h7 : br0.bitIndex + 7 ≤ br0.data.size * 8 := by
    have h79 : br0.bitIndex + 7 ≤ br0.bitIndex + 9 := by omega
    exact le_trans h79 h9'
  have hread7 :
      br0.readBitsFastU32 7 h7 = (bits % 2 ^ 7, br1) := by
    simpa [br0, br1, bwAll, lenTot, eobNoTailWriter, eobNoTailStartReader, eobNoTailAfterReader]
      using
        (readBitsFastU32_readerAt_writeBits_prefix (bw := bw) (bits := bits) (len := lenTot) (k := 7)
          (hk := by
            have hlen : lenTot = 7 := by decide
            omega)
          (hbit := hbit) (hcur := hcur))
  have hbitsZero : bits = 0 := by
    native_decide
  have h7res : br0.readBitsFastU32 7 h7 = (0, br1) := by
    simpa [hbitsZero] using hread7
  have h7aux : br0.readBitsFastU32 7 h7 = br0.readBitsAux 7 := by
    simpa using (readBitsFastU32_eq_readBitsAux (br := br0) (n := 7) (h := h7))
  have h7aux' : br0.readBitsAux 7 = (0, br1) := by
    calc
      br0.readBitsAux 7 = br0.readBitsFastU32 7 h7 := by simpa using h7aux.symm
      _ = (0, br1) := h7res
  have h9aux : br0.readBitsFastU32 9 h9 = br0.readBitsAux 9 := by
    simpa using (readBitsFastU32_eq_readBitsAux (br := br0) (n := 9) (h := h9))
  rcases hrest2 : br1.readBitsAux 2 with ⟨bits2, br2⟩
  have hsplit := readBitsAux_split (br := br0) (k := 7) (n := 2)
  have haux9shape : br0.readBitsAux 9 = (0 ||| (bits2 <<< 7), br2) := by
    simpa [h7aux', hrest2] using hsplit
  have hbits9mod : (br0.readBitsFastU32 9 h9).1 % 2 ^ 7 = 0 := by
    have hmod : (br0.readBitsAux 9).1 % 2 ^ 7 = 0 := by
      rw [haux9shape]
      have hmul : (bits2 <<< 7) % 2 ^ 7 = 0 := by
        simpa [Nat.shiftLeft_eq] using (Nat.mul_mod_right bits2 (2 ^ 7))
      simpa using hmul
    simpa [h9aux] using hmod
  have hrow7 : fixedLitLenRow7[((br0.readBitsFastU32 9 h9).1 % 2 ^ 7)]? = some (some 256) := by
    simpa [hbits9mod] using (by decide : fixedLitLenRow7[0]? = some (some 256))
  unfold decodeFixedLiteralSymFast9
  have hread7' : br0.bitIndex + 7 ≤ br0.data.size * 8 := h7
  simpa [br0, br1, h9, h7, hrow7, h7res]

set_option maxRecDepth 200000 in
lemma decodeFixedLiteralSymFast9_eobNoTail
    (bw : BitWriter) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedLiteralSymFast9 (eobNoTailStartReader bw hbit) =
      some (256, eobNoTailAfterReader bw hbit) := by
  by_cases h9 : (eobNoTailStartReader bw hbit).bitIndex + 9 ≤ (eobNoTailStartReader bw hbit).data.size * 8
  · exact decodeFixedLiteralSymFast9_eobNoTail_h9 (bw := bw) (hbit := hbit) (hcur := hcur) h9
  · let sym : Nat := 256
    let codeLen := fixedLitLenCode sym
    let bits := reverseBits codeLen.1 codeLen.2
    let lenTot := codeLen.2
    let bwAll := eobNoTailWriter bw
    let br0 := eobNoTailStartReader bw hbit
    let br1 := eobNoTailAfterReader bw hbit
    have hdecodeSlow :=
      decodeFixedLiteralSym_readerAt_writeBits' (bw := bw) (sym := sym)
        (restBits := 0) (restLen := 0) (by decide) hbit hcur
    have hdecodeSlow' : decodeFixedLiteralSym br0 = some (sym, br1) := by
      simpa [sym, codeLen, bits, lenTot, bwAll, br0, br1, eobNoTailWriter, eobNoTailStartReader,
        eobNoTailAfterReader] using hdecodeSlow
    unfold decodeFixedLiteralSymFast9
    simpa [h9] using hdecodeSlow'

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_eob_eobNoTail
    (fuel : Nat) (bw : BitWriter) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedBlockFuelFast (fuel + 1) (eobNoTailStartReader bw hbit) out =
      some (eobNoTailAfterReader bw hbit, out) := by
  have hdecodeSym : decodeFixedLiteralSymFast9 (eobNoTailStartReader bw hbit) =
      some (256, eobNoTailAfterReader bw hbit) := by
    exact decodeFixedLiteralSymFast9_eobNoTail (bw := bw) (hbit := hbit) (hcur := hcur)
  have hnotLit : ¬ (256 : Nat) < 256 := by decide
  have heob : ((256 : Nat) == 256) = true := by decide
  simpa using
    (decodeFixedBlockFuelFast_step_eob_of_decodes
      (fuel := fuel) (br := eobNoTailStartReader bw hbit) (br' := eobNoTailAfterReader bw hbit)
      (out := out) (sym := 256) (hdecodeSym := hdecodeSym) (hnotLit := hnotLit) (heob := heob))

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_literalRepeatBitsTail_readerAt_writeBits_exists
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (n tailBits tailLen : Nat) (out : ByteArray)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    ∃ brAfter,
      decodeFixedBlockFuelFast (fuel + n)
        (BitWriter.readerAt bw
          (BitWriter.writeBits bw
            (literalRepeatBitsTail b n tailBits tailLen).1
            (literalRepeatBitsTail b n tailBits tailLen).2).flush
          (flush_size_writeBits_le bw
            (literalRepeatBitsTail b n tailBits tailLen).1
            (literalRepeatBitsTail b n tailBits tailLen).2) hbit) out =
        decodeFixedBlockFuelFast fuel brAfter (pushRepeat out b n) := by
  induction n generalizing fuel bw out tailBits tailLen hbit hcur with
  | zero =>
      refine ⟨BitWriter.readerAt bw (BitWriter.writeBits bw tailBits tailLen).flush
        (flush_size_writeBits_le bw tailBits tailLen) hbit, ?_⟩
      simp [literalRepeatBitsTail, pushRepeat]
  | succ n ih =>
      let rest := literalRepeatBitsTail b n tailBits tailLen
      let tailBits' := rest.1
      let tailLen' := rest.2
      let codeLen := fixedLitLenCode b.toNat
      let bits := reverseBits codeLen.1 codeLen.2
      let bitsTot := bits ||| (tailBits' <<< codeLen.2)
      let lenTot := codeLen.2 + tailLen'
      let bwAll := BitWriter.writeBits bw bitsTot lenTot
      let br0 := BitWriter.readerAt bw bwAll.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
      have htail2' : 2 ≤ tailLen' := by
        dsimp [tailLen']
        exact literalRepeatBitsTail_len_ge_two b n tailBits tailLen htail2
      have hbit1 : (BitWriter.writeBits bw bitsTot codeLen.2).bitPos < 8 := by
        exact bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit
      have hcur1 : (BitWriter.writeBits bw bitsTot codeLen.2).curClearAbove := by
        exact curClearAbove_writeBits bw bitsTot codeLen.2 hbit hcur
      have hstep :=
        decodeFixedBlockFuelFast_step_literal_readerAt_writeBits
          (fuel := fuel + n) (bw := bw) (b := b) (tailBits := tailBits') (tailLen := tailLen')
          (out := out) (htail2 := htail2') (hbit := hbit) (hcur := hcur)
      have hstep' :
          decodeFixedBlockFuelFast (fuel + (n + 1)) br0 out =
            decodeFixedBlockFuelFast (fuel + n)
              (BitWriter.readerAt (BitWriter.writeBits bw bitsTot codeLen.2) bwAll.flush
                (by
                  have hk : codeLen.2 ≤ lenTot := by omega
                  simpa [bwAll, lenTot] using (flush_size_writeBits_prefix bw bitsTot codeLen.2 lenTot hk))
                hbit1)
              (out.push b) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, rest, tailBits', tailLen', codeLen, bits,
          bitsTot, lenTot, bwAll, br0] using hstep
      have hbitsLt : bits < 2 ^ codeLen.2 := by
        simpa [bits] using (reverseBits_lt codeLen.1 codeLen.2)
      have hconcat :
          BitWriter.writeBits bw bitsTot lenTot =
            BitWriter.writeBits (BitWriter.writeBits bw bits codeLen.2) tailBits' tailLen' := by
        simpa [bitsTot, lenTot] using (writeBits_concat bw bits tailBits' codeLen.2 tailLen' hbitsLt)
      have hmod : bitsTot % 2 ^ codeLen.2 = bits := by
        have hmod' : bitsTot % 2 ^ codeLen.2 = bits % 2 ^ codeLen.2 := by
          simpa [bitsTot] using
            (mod_two_pow_or_shift (a := bits) (b := tailBits') (k := codeLen.2) (len := codeLen.2)
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
      have hih :=
        ih (fuel := fuel) (bw := BitWriter.writeBits bw bitsTot codeLen.2)
          (out := out.push b) (tailBits := tailBits) (tailLen := tailLen)
          (hbit := hbit1) (hcur := hcur1)
      have hih' := hih htail2
      rcases hih' with ⟨brAfter, hih''⟩
      have hihNorm :
          decodeFixedBlockFuelFast (fuel + n)
              (BitWriter.readerAt (BitWriter.writeBits bw bitsTot codeLen.2) bwAll.flush
                (by
                  have hk : codeLen.2 ≤ lenTot := by omega
                  simpa [bwAll, lenTot] using (flush_size_writeBits_prefix bw bitsTot codeLen.2 lenTot hk))
                hbit1)
              (out.push b) =
            decodeFixedBlockFuelFast fuel brAfter (pushRepeat (out.push b) b n) := by
        simpa [rest, tailBits', tailLen', codeLen, bits, bitsTot, lenTot, bwAll, hconcat, hwriteBits] using hih''
      refine ⟨brAfter, ?_⟩
      have hmain := hstep'.trans hihNorm
      simpa [literalRepeatBitsTail_succ, rest, tailBits', tailLen', codeLen, bits, bitsTot, lenTot, bwAll,
        pushRepeat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain

def literalRepeatTailWriter (bw : BitWriter) (b : UInt8) (n tailBits tailLen : Nat) : BitWriter :=
  match n with
  | 0 => bw
  | n + 1 =>
      let rest := literalRepeatBitsTail b n tailBits tailLen
      literalRepeatTailWriter (literalTailWriter bw b rest.1 rest.2) b n tailBits tailLen

lemma literalRepeatTailWriter_bitPos_lt
    (bw : BitWriter) (b : UInt8) (n tailBits tailLen : Nat) (hbit : bw.bitPos < 8) :
    (literalRepeatTailWriter bw b n tailBits tailLen).bitPos < 8 := by
  induction n generalizing bw with
  | zero =>
      simpa [literalRepeatTailWriter]
  | succ n ih =>
      dsimp [literalRepeatTailWriter]
      exact ih (bw := literalTailWriter bw b (literalRepeatBitsTail b n tailBits tailLen).1
        (literalRepeatBitsTail b n tailBits tailLen).2)
        (literalTailWriter_bitPos_lt bw b (literalRepeatBitsTail b n tailBits tailLen).1
          (literalRepeatBitsTail b n tailBits tailLen).2 hbit)

lemma literalRepeatTailWriter_curClearAbove
    (bw : BitWriter) (b : UInt8) (n tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    (literalRepeatTailWriter bw b n tailBits tailLen).curClearAbove := by
  induction n generalizing bw with
  | zero =>
      simpa [literalRepeatTailWriter]
  | succ n ih =>
      dsimp [literalRepeatTailWriter]
      exact ih
        (bw := literalTailWriter bw b (literalRepeatBitsTail b n tailBits tailLen).1
          (literalRepeatBitsTail b n tailBits tailLen).2)
        (hbit := literalTailWriter_bitPos_lt bw b (literalRepeatBitsTail b n tailBits tailLen).1
          (literalRepeatBitsTail b n tailBits tailLen).2 hbit)
        (hcur := literalTailWriter_curClearAbove bw b (literalRepeatBitsTail b n tailBits tailLen).1
          (literalRepeatBitsTail b n tailBits tailLen).2 hbit hcur)

def literalRepeatTailStartReader (bw : BitWriter) (b : UInt8) (n tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  let bwTail := literalRepeatTailWriter bw b n tailBits tailLen
  BitWriter.readerAt bwTail (BitWriter.writeBits bwTail tailBits tailLen).flush
    (flush_size_writeBits_le bwTail tailBits tailLen)
    (literalRepeatTailWriter_bitPos_lt bw b n tailBits tailLen hbit)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_literalRepeatBitsTail_readerAt_writeBits_tail
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (n tailBits tailLen : Nat) (out : ByteArray)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeFixedBlockFuelFast (fuel + n)
      (BitWriter.readerAt bw
        (BitWriter.writeBits bw
          (literalRepeatBitsTail b n tailBits tailLen).1
          (literalRepeatBitsTail b n tailBits tailLen).2).flush
        (flush_size_writeBits_le bw
          (literalRepeatBitsTail b n tailBits tailLen).1
          (literalRepeatBitsTail b n tailBits tailLen).2) hbit) out =
      decodeFixedBlockFuelFast fuel
        (literalRepeatTailStartReader bw b n tailBits tailLen hbit) (pushRepeat out b n) := by
  induction n generalizing fuel bw out tailBits tailLen hbit hcur with
  | zero =>
      simp [literalRepeatTailStartReader, literalRepeatTailWriter, literalRepeatBitsTail_zero, pushRepeat]
  | succ n ih =>
      let rest := literalRepeatBitsTail b n tailBits tailLen
      let tailBits' := rest.1
      let tailLen' := rest.2
      have htail2' : 2 ≤ tailLen' := by
        dsimp [tailLen']
        exact literalRepeatBitsTail_len_ge_two b n tailBits tailLen htail2
      have hstep :=
        decodeFixedBlockFuelFast_step_literal_readerAt_writeBits_tail
          (fuel := fuel + n) (bw := bw) (b := b) (tailBits := tailBits') (tailLen := tailLen')
          (out := out) (htail2 := htail2') (hbit := hbit) (hcur := hcur)
      have hbit1 : (literalTailWriter bw b tailBits' tailLen').bitPos < 8 := by
        exact literalTailWriter_bitPos_lt bw b tailBits' tailLen' hbit
      have hcur1 : (literalTailWriter bw b tailBits' tailLen').curClearAbove := by
        exact literalTailWriter_curClearAbove bw b tailBits' tailLen' hbit hcur
      have hih :=
        ih (fuel := fuel) (bw := literalTailWriter bw b tailBits' tailLen')
          (out := out.push b) (tailBits := tailBits) (tailLen := tailLen)
          (htail2 := htail2) (hbit := hbit1) (hcur := hcur1)
      have hih' :
          decodeFixedBlockFuelFast (fuel + n)
            (literalTailStartReader bw b tailBits' tailLen' hbit) (out.push b) =
              decodeFixedBlockFuelFast fuel
                (literalRepeatTailStartReader (literalTailWriter bw b tailBits' tailLen')
                  b n tailBits tailLen hbit1) (pushRepeat (out.push b) b n) := by
        simpa [rest, tailBits', tailLen', literalTailStartReader] using hih
      have htailEq :
          literalRepeatTailStartReader bw b (n + 1) tailBits tailLen hbit =
            literalRepeatTailStartReader (literalTailWriter bw b tailBits' tailLen')
              b n tailBits tailLen hbit1 := by
        rfl
      have hpush : pushRepeat (out.push b) b n = pushRepeat out b (n + 1) := by
        simpa using (pushRepeat_push_eq out b n).symm
      have hmain := hstep.trans hih'
      have hmain' :
          decodeFixedBlockFuelFast (fuel + (n + 1))
            (BitWriter.readerAt bw
              (BitWriter.writeBits bw
                (literalRepeatBitsTail b (n + 1) tailBits tailLen).1
                (literalRepeatBitsTail b (n + 1) tailBits tailLen).2).flush
              (flush_size_writeBits_le bw
                (literalRepeatBitsTail b (n + 1) tailBits tailLen).1
                (literalRepeatBitsTail b (n + 1) tailBits tailLen).2) hbit) out =
          decodeFixedBlockFuelFast fuel
            (literalRepeatTailStartReader (literalTailWriter bw b tailBits' tailLen')
              b n tailBits tailLen hbit1) (pushRepeat (out.push b) b n) := by
        simpa [literalRepeatBitsTail_succ, rest, tailBits', tailLen',
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain
      rw [htailEq, ← hpush]
      exact hmain'

def dist1ChunkLoopTailLitsTailStartReader
    (bw : BitWriter) (remaining : Nat) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
  if _hrem : 3 ≤ remaining then
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
    dist1ChunkLoopTailLitsTailStartReader bwChunk rem' b tailBits tailLen hbitChunk
  else
    literalRepeatTailStartReader bw b remaining tailBits tailLen hbit
termination_by remaining
decreasing_by
  have hlt := chooseFixedMatchChunkLen_sub_lt remaining _hrem
  simpa [rem'] using hlt

def dist1ChunkLoopTailLitsTailStartReaderStep
    (bw : BitWriter) (remaining : Nat) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) : BitReader :=
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
  dist1ChunkLoopTailLitsTailStartReader bwChunk rem' b tailBits tailLen hbitChunk

lemma dist1ChunkLoopTailLitsTailStartReader_of_ge3
    (bw : BitWriter) (remaining : Nat) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) (hrem : 3 ≤ remaining) :
    dist1ChunkLoopTailLitsTailStartReader bw remaining b tailBits tailLen hbit =
      dist1ChunkLoopTailLitsTailStartReaderStep bw remaining b tailBits tailLen hbit := by
  simpa [dist1ChunkLoopTailLitsTailStartReaderStep, hrem] using
    (dist1ChunkLoopTailLitsTailStartReader.eq_1
      (bw := bw) (remaining := remaining) (b := b)
      (tailBits := tailBits) (tailLen := tailLen) (hbit := hbit))

lemma dist1ChunkLoopTailLitsTailStartReader_of_lt3
    (bw : BitWriter) (remaining : Nat) (b : UInt8) (tailBits tailLen : Nat)
    (hbit : bw.bitPos < 8) (hrem : ¬ 3 ≤ remaining) :
    dist1ChunkLoopTailLitsTailStartReader bw remaining b tailBits tailLen hbit =
      literalRepeatTailStartReader bw b remaining tailBits tailLen hbit := by
  rw [dist1ChunkLoopTailLitsTailStartReader.eq_1]
  simp [hrem]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_dist1ChunkLoopTailLits_readerAt_writeBits_tail_of_lt3
    (fuel : Nat) (bw : BitWriter) (remaining tailBits tailLen : Nat)
    (out : ByteArray) (b : UInt8)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    (hrem : ¬ 3 ≤ remaining) :
    let remLit := dist1ChunkLoopRem remaining
    let litTail := literalRepeatBitsTail b remLit tailBits tailLen
    let bitsLen := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
    decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit)
      (BitWriter.readerAt bw
        (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
        (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out =
      decodeFixedBlockFuelFast fuel
        (dist1ChunkLoopTailLitsTailStartReader bw remaining b tailBits tailLen hbit)
        (pushRepeat out b remaining) := by
  let remLit := dist1ChunkLoopRem remaining
  let litTail := literalRepeatBitsTail b remLit tailBits tailLen
  let bitsLen := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
  have hremLit : remLit = remaining := by
    dsimp [remLit]
    simpa using (dist1ChunkLoopRem_of_lt3 remaining hrem)
  have hsteps0 : dist1ChunkLoopSteps remaining = 0 := by
    exact dist1ChunkLoopSteps_of_lt3 remaining hrem
  have hbits0 : bitsLen = litTail := by
    dsimp [bitsLen]
    simpa [litTail] using (dist1ChunkLoopBitsTail_of_lt3 remaining litTail.1 litTail.2 hrem)
  have htail2Lit : 2 ≤ litTail.2 := by
    dsimp [litTail]
    exact literalRepeatBitsTail_len_ge_two b remLit tailBits tailLen htail2
  have hbase :=
    decodeFixedBlockFuelFast_literalRepeatBitsTail_readerAt_writeBits_tail
      (fuel := fuel) (bw := bw) (b := b) (n := remaining) (tailBits := tailBits) (tailLen := tailLen)
      (out := out) (htail2 := htail2) (hbit := hbit) (hcur := hcur)
  have hreader :
      dist1ChunkLoopTailLitsTailStartReader bw remaining b tailBits tailLen hbit =
        literalRepeatTailStartReader bw b remaining tailBits tailLen hbit := by
    exact dist1ChunkLoopTailLitsTailStartReader_of_lt3
      (bw := bw) (remaining := remaining) (b := b)
      (tailBits := tailBits) (tailLen := tailLen) (hbit := hbit) (hrem := hrem)
  have hbits0' :
      dist1ChunkLoopBitsTail remaining
        (literalRepeatBitsTail b remaining tailBits tailLen).1
        (literalRepeatBitsTail b remaining tailBits tailLen).2 =
      literalRepeatBitsTail b remaining tailBits tailLen := by
    simpa using
      (dist1ChunkLoopBitsTail_of_lt3 remaining
        (literalRepeatBitsTail b remaining tailBits tailLen).1
        (literalRepeatBitsTail b remaining tailBits tailLen).2 hrem)
  simpa [remLit, litTail, bitsLen, hremLit, hsteps0, hbits0, hbits0', hreader,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbase

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_match_of_decodes
    (fuel : Nat) (br br' br'' br''' br'''' : BitReader)
    (out out' : ByteArray)
    (sym extra len distSym extraD distance : Nat)
    (hdecodeSym : decodeFixedLiteralSymFast9 br = some (sym, br'))
    (hnotLit : ¬ sym < 256)
    (hnotEob : (sym == 256) = false)
    (hsym : 257 ≤ sym ∧ sym ≤ 285)
    (hextra :
      extra =
        Array.getInternal lengthExtra (sym - 257) (by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt))
    (hbits : br'.bitIndex + extra ≤ br'.data.size * 8)
    (hdecodeLen :
      decodeLength sym br' hsym
        (by
          have hbits' : br'.bitIndex +
              lengthExtra[sym - 257]'(by
                have hidxle : sym - 257 ≤ 28 := by omega
                have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                have hsize : lengthExtra.size = 29 := by decide
                simpa [hsize] using hidxlt) ≤ br'.data.size * 8 := by
            simpa [hextra] using hbits
          simpa using hbits') = (len, br''))
    (hdecodeDistSym : decodeFixedDistanceSym br'' = some (distSym, br'''))
    (hdist : distSym < distBases.size)
    (hextraD :
      extraD =
        Array.getInternal distExtra distSym (by
          have hDistExtraSize : distExtra.size = 30 := by decide
          have hDistBasesSize : distBases.size = 30 := by decide
          simpa [hDistExtraSize, hDistBasesSize] using hdist))
    (hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8)
    (hdecodeDist :
      decodeDistance distSym br''' hdist
        (by
          have hbitsD' : br'''.bitIndex +
              distExtra[distSym]'(by
                have hDistExtraSize : distExtra.size = 30 := by decide
                have hDistBasesSize : distBases.size = 30 := by decide
                simpa [hDistExtraSize, hDistBasesSize] using hdist) ≤ br'''.data.size * 8 := by
            simpa [hextraD] using hbitsD
          simpa using hbitsD') = (distance, br''''))
    (hcopy : copyDistance out distance len = some out') :
    decodeFixedBlockFuelFast (fuel + 1) br out =
      decodeFixedBlockFuelFast fuel br'''' out' := by
  let recCall := decodeFixedBlockFuelFast fuel br'''' out'
  change decodeFixedBlockFuelFast (fuel + 1) br out = recCall
  have hrec : decodeFixedBlockFuelFast fuel br'''' out' = recCall := rfl
  rw [decodeFixedBlockFuelFast.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  change
    (if sym < 256 then
      decodeFixedBlockFuelFast fuel br' (out.push (u8 sym))
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
        let (distSym, br''') ← decodeFixedDistanceSym br''
        if hdist : distSym < distBases.size then
          let extraD := Array.getInternal distExtra distSym (by
            have hDistExtraSize : distExtra.size = 30 := by decide
            have hDistBasesSize : distBases.size = 30 := by decide
            simpa [hDistExtraSize, hDistBasesSize] using hdist)
          if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
            let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
            let out' ← copyDistance out distance len
            decodeFixedBlockFuelFast fuel br'''' out'
          else
            none
        else
          none
      else
        none
    else
      none) = recCall
  rw [if_neg hnotLit]
  rw [if_neg (by simpa using hnotEob)]
  rw [dif_pos hsym]
  have hLetExtra :
      (let idx := sym - 257
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
           let (len, br'') := decodeLength sym br' hsym (by simpa using hbits)
           let (distSym, br''') ← decodeFixedDistanceSym br''
           if hdist : distSym < distBases.size then
             let extraD := Array.getInternal distExtra distSym (by
               have hDistExtraSize : distExtra.size = 30 := by decide
               have hDistBasesSize : distBases.size = 30 := by decide
               simpa [hDistExtraSize, hDistBasesSize] using hdist)
             if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
               do
                 let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
                 let out' ← copyDistance out distance len
                 decodeFixedBlockFuelFast fuel br'''' out'
             else
               none
           else
             none
       else
         none) =
      (if hbits : br'.bitIndex + extra ≤ br'.data.size * 8 then
        do
          let (len, br'') := decodeLength sym br' hsym (by simpa [hextra] using hbits)
          let (distSym, br''') ← decodeFixedDistanceSym br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              do
                let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
                let out' ← copyDistance out distance len
                decodeFixedBlockFuelFast fuel br'''' out'
            else
              none
          else
            none
      else
        none) := by
    simpa [hextra]
  rw [hLetExtra]
  rw [dif_pos hbits]
  rw [hdecodeLen]
  have hPairLen :
      (match (len, br'') with
      | (len, br'') =>
        do
          let __discr ← decodeFixedDistanceSym br''
          match __discr with
          | (distSym, br''') =>
            if hdist : distSym < distBases.size then
              let extraD := Array.getInternal distExtra distSym (by
                have hDistExtraSize : distExtra.size = 30 := by decide
                have hDistBasesSize : distBases.size = 30 := by decide
                simpa [hDistExtraSize, hDistBasesSize] using hdist)
              if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
                do
                  let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
                  let out' ← copyDistance out distance len
                  decodeFixedBlockFuelFast fuel br'''' out'
              else
                none
            else
              none) =
      (do
        let __discr ← decodeFixedDistanceSym br''
        match __discr with
        | (distSym, br''') =>
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              do
                let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
                let out' ← copyDistance out distance len
                decodeFixedBlockFuelFast fuel br'''' out'
            else
              none
          else
            none) := by
    rfl
  rw [hPairLen]
  change
    (do
      let __discr ← decodeFixedDistanceSym br''
      match __discr with
      | (distSym, br''') =>
        if hdist : distSym < distBases.size then
          let extraD := Array.getInternal distExtra distSym (by
            have hDistExtraSize : distExtra.size = 30 := by decide
            have hDistBasesSize : distBases.size = 30 := by decide
            simpa [hDistExtraSize, hDistBasesSize] using hdist)
          if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
            do
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeFixedBlockFuelFast fuel br'''' out'
          else
            none
        else
          none) = recCall
  rw [hdecodeDistSym]
  rw [option_do_some]
  have hPairDistSym :
      (match (distSym, br''') with
      | (distSym, br''') =>
        if hdist : distSym < distBases.size then
          let extraD := Array.getInternal distExtra distSym (by
            have hDistExtraSize : distExtra.size = 30 := by decide
            have hDistBasesSize : distBases.size = 30 := by decide
            simpa [hDistExtraSize, hDistBasesSize] using hdist)
          if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
            do
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeFixedBlockFuelFast fuel br'''' out'
          else
            none
        else
          none) =
      (if hdist : distSym < distBases.size then
        let extraD := Array.getInternal distExtra distSym (by
          have hDistExtraSize : distExtra.size = 30 := by decide
          have hDistBasesSize : distBases.size = 30 := by decide
          simpa [hDistExtraSize, hDistBasesSize] using hdist)
        if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
          do
            let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
            let out' ← copyDistance out distance len
            decodeFixedBlockFuelFast fuel br'''' out'
        else
          none
      else
        none) := by
    rfl
  rw [hPairDistSym]
  change
    (if hdist : distSym < distBases.size then
      let extraD := Array.getInternal distExtra distSym (by
        have hDistExtraSize : distExtra.size = 30 := by decide
        have hDistBasesSize : distBases.size = 30 := by decide
        simpa [hDistExtraSize, hDistBasesSize] using hdist)
      if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
        do
          let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
          let out' ← copyDistance out distance len
          decodeFixedBlockFuelFast fuel br'''' out'
      else
        none
    else
      none) = recCall
  rw [dif_pos hdist]
  have hLetExtraD :
      (let extraD := Array.getInternal distExtra distSym (by
         have hDistExtraSize : distExtra.size = 30 := by decide
         have hDistBasesSize : distBases.size = 30 := by decide
         simpa [hDistExtraSize, hDistBasesSize] using hdist)
       if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
         do
           let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
           let out' ← copyDistance out distance len
           decodeFixedBlockFuelFast fuel br'''' out'
       else
         none) =
      (if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
        do
          let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa [hextraD] using hbitsD)
          let out' ← copyDistance out distance len
          decodeFixedBlockFuelFast fuel br'''' out'
      else
        none) := by
    simpa [hextraD]
  rw [hLetExtraD]
  rw [dif_pos hbitsD]
  rw [hdecodeDist]
  have hPairDist :
      (match (distance, br'''') with
      | (distance, br'''') =>
        do
          let out' ← copyDistance out distance len
          decodeFixedBlockFuelFast fuel br'''' out') =
      (do
        let out' ← copyDistance out distance len
        decodeFixedBlockFuelFast fuel br'''' out') := by
    rfl
  rw [hPairDist]
  change
    (do
      let out' ← copyDistance out distance len
      decodeFixedBlockFuelFast fuel br'''' out') = recCall
  rw [hcopy]
  rw [option_do_some]

set_option maxRecDepth 200000 in
-- Decoding a length code and its extra bits recovers the encoded match length.
lemma decodeLength_readerAt_writeBits_prefix
    (bw : BitWriter) (sym extraBits extraLen restBits restLen lenOut : Nat)
    (hsym : 257 ≤ sym ∧ sym ≤ 285)
    (hidxBase : sym - 257 < lengthBases.size)
    (hidxExtra : sym - 257 < lengthExtra.size)
    (hextra : extraLen = Array.getInternal lengthExtra (sym - 257) hidxExtra)
    (hbase : Array.getInternal lengthBases (sym - 257) hidxBase + extraBits = lenOut)
    (hbitsLt : extraBits < 2 ^ extraLen)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := extraBits ||| (restBits <<< extraLen)
    let lenTot := extraLen + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeLength sym br hsym
      (by
        have hread :=
          readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := extraLen)
            (hk := by omega) (hbit := hbit)
        simpa [br, bw', lenTot, hextra] using hread) =
      (lenOut,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot extraLen) bw'.flush
          (by
            have hk : extraLen ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot extraLen lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot extraLen hbit)) := by
  let bitsTot := extraBits ||| (restBits <<< extraLen)
  let lenTot := extraLen + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let brExtra := BitWriter.readerAt (BitWriter.writeBits bw bitsTot extraLen) bw'.flush
    (by
      have hk : extraLen ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot extraLen lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot extraLen hbit)
  have hreadExtra : br.bitIndex + extraLen ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := extraLen)
        (hk := by omega) (hbit := hbit))
  have hbitsRead :
      br.readBits extraLen hreadExtra = (bitsTot % 2 ^ extraLen, brExtra) := by
    simpa [br, bw', brExtra, lenTot] using
      (readBits_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := extraLen)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hmodExtra : bitsTot % 2 ^ extraLen = extraBits := by
    have h := mod_two_pow_or_shift (a := extraBits) (b := restBits) (k := extraLen) (len := extraLen)
      (by exact le_rfl)
    have hmod : extraBits % 2 ^ extraLen = extraBits := Nat.mod_eq_of_lt hbitsLt
    simpa [bitsTot, hmod] using h
  have hbitsRead' :
      br.readBits extraLen hreadExtra = (extraBits, brExtra) := by
    calc
      br.readBits extraLen hreadExtra = (bitsTot % 2 ^ extraLen, brExtra) := hbitsRead
      _ = (extraBits, brExtra) := by simp [hmodExtra]
  have hidxEqBase : Array.getInternal lengthBases (sym - 257) hidxBase =
      Array.getInternal lengthBases (sym - 257)
        (by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : lengthBases.size = 29 := by decide
          simpa [hsize] using hidxlt) := by
    have hprf : hidxBase =
        (by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : lengthBases.size = 29 := by decide
          simpa [hsize] using hidxlt) := Subsingleton.elim _ _
    simpa [hprf]
  have hidxEqExtra : Array.getInternal lengthExtra (sym - 257) hidxExtra =
      Array.getInternal lengthExtra (sym - 257)
        (by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt) := by
    have hprf : hidxExtra =
        (by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt) := Subsingleton.elim _ _
    simpa [hprf]
  have hcanonExtra : lengthExtra[sym - 257]'(by
      have hidxlt : sym - 257 < 29 := by omega
      have hsize : lengthExtra.size = 29 := by decide
      simpa [hsize] using hidxlt) = extraLen := by
    calc
      lengthExtra[sym - 257]'(by
          have hidxlt : sym - 257 < 29 := by omega
          have hsize : lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt)
          = Array.getInternal lengthExtra (sym - 257)
              (by
                have hidxlt : sym - 257 < 29 := by omega
                have hsize : lengthExtra.size = 29 := by decide
                simpa [hsize] using hidxlt) := rfl
      _ = Array.getInternal lengthExtra (sym - 257) hidxExtra := by
            symm
            exact hidxEqExtra
      _ = extraLen := by simpa using hextra.symm
  have hcanonBasePlus : lengthBases[sym - 257]'(by
      have hidxlt : sym - 257 < 29 := by omega
      have hsize : lengthBases.size = 29 := by decide
      simpa [hsize] using hidxlt) + extraBits = lenOut := by
    have hcanonBase : lengthBases[sym - 257]'(by
        have hidxlt : sym - 257 < 29 := by omega
        have hsize : lengthBases.size = 29 := by decide
        simpa [hsize] using hidxlt) =
        Array.getInternal lengthBases (sym - 257) hidxBase := by
      calc
        lengthBases[sym - 257]'(by
            have hidxlt : sym - 257 < 29 := by omega
            have hsize : lengthBases.size = 29 := by decide
            simpa [hsize] using hidxlt)
            = Array.getInternal lengthBases (sym - 257)
                (by
                  have hidxlt : sym - 257 < 29 := by omega
                  have hsize : lengthBases.size = 29 := by decide
                  simpa [hsize] using hidxlt) := rfl
        _ = Array.getInternal lengthBases (sym - 257) hidxBase := hidxEqBase.symm
    calc
      lengthBases[sym - 257]'(by
          have hidxlt : sym - 257 < 29 := by omega
          have hsize : lengthBases.size = 29 := by decide
          simpa [hsize] using hidxlt) + extraBits
          = Array.getInternal lengthBases (sym - 257) hidxBase + extraBits := by
              rw [hcanonBase]
      _ = lenOut := hbase
  by_cases hextra0 : extraLen = 0
  · have hbrEq : brExtra = br := by
      apply BitReader.ext
      all_goals
        simp [brExtra, br, bw', bitsTot, lenTot, hextra0, writeBits_zero]
    have hbaseCanon0 :
        lengthBases[sym - 257]'(by
          have hidxlt : sym - 257 < 29 := by omega
          have hsize : lengthBases.size = 29 := by decide
          simpa [hsize] using hidxlt) = lenOut := by
      have hbits0 : extraBits = 0 := by
        have : extraBits < 1 := by simpa [hextra0] using hbitsLt
        omega
      have : lengthBases[sym - 257]'(by
          have hidxlt : sym - 257 < 29 := by omega
          have hsize : lengthBases.size = 29 := by decide
          simpa [hsize] using hidxlt) + extraBits = lenOut := hcanonBasePlus
      omega
    have hbitsArg :
        br.bitIndex +
            lengthExtra[sym - 257]'(by
              have hidxlt : sym - 257 < 29 := by omega
              have hsize : lengthExtra.size = 29 := by decide
              simpa [hsize] using hidxlt) ≤ br.data.size * 8 := by
      simpa [br, bw', lenTot, hextra, hextra0] using hreadExtra
    have hdecode :
        decodeLength sym br hsym hbitsArg = (lenOut, br) := by
      unfold decodeLength
      have hcanonExtra0 : lengthExtra[sym - 257]'(by
          have hidxlt : sym - 257 < 29 := by omega
          have hsize : lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt) = 0 := by
        simpa [hcanonExtra] using hextra0
      simp [hcanonExtra0, hbaseCanon0, hidxEqBase, hidxEqExtra]
    simpa [bitsTot, lenTot, bw', br, brExtra, hbrEq] using hdecode
  · have hbitsArg :
      br.bitIndex +
          lengthExtra[sym - 257]'(by
            have hidxlt : sym - 257 < 29 := by omega
            have hsize : lengthExtra.size = 29 := by decide
            simpa [hsize] using hidxlt) ≤ br.data.size * 8 := by
      simpa [br, bw', lenTot, hextra] using hreadExtra
    have hdecode :
        decodeLength sym br hsym hbitsArg = (lenOut, brExtra) := by
      unfold decodeLength
      have hcanonExtraNe0 :
          ¬ lengthExtra[sym - 257]'(by
              have hidxlt : sym - 257 < 29 := by omega
              have hsize : lengthExtra.size = 29 := by decide
              simpa [hsize] using hidxlt) = 0 := by
        simpa [hcanonExtra] using hextra0
      have hreadEq :
          br.readBits
              (lengthExtra[sym - 257]'(by
                have hidxlt : sym - 257 < 29 := by omega
                have hsize : lengthExtra.size = 29 := by decide
                simpa [hsize] using hidxlt))
              hbitsArg
            = br.readBits extraLen hreadExtra := by
        have hbitsArg' : br.bitIndex + extraLen ≤ br.data.size * 8 := by
          simpa [hcanonExtra] using hbitsArg
        calc
          br.readBits
              (lengthExtra[sym - 257]'(by
                have hidxlt : sym - 257 < 29 := by omega
                have hsize : lengthExtra.size = 29 := by decide
                simpa [hsize] using hidxlt))
              hbitsArg
              = br.readBits extraLen hbitsArg' := by
                  simp [hcanonExtra]
          _ = br.readBits extraLen hreadExtra := by
                exact readBits_proof_irrel (br := br) (n := extraLen) (h1 := hbitsArg') (h2 := hreadExtra)
      simp [hcanonExtraNe0]
      rw [hreadEq, hbitsRead']
      simp [hcanonBasePlus]
    simpa [bitsTot, lenTot, bw', br, brExtra] using hdecode

lemma decodeFixedLiteralSymFast9_readerAt_writeBits_fixedLenMatchInfo
    (bw : BitWriter) (matchLen restBits restLen : Nat)
    (hlen : 3 ≤ matchLen ∧ matchLen ≤ 258) (hrest2 : 2 ≤ restLen)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let info := fixedLenMatchInfo matchLen
    let sym := info.1
    let _extraBits := info.2.1
    let _extraLen := info.2.2
    let codeLen := fixedLitLenCode sym
    let code := codeLen.1
    let len := codeLen.2
    let bits := reverseBits code len
    let bitsTot := bits ||| (restBits <<< len)
    let lenTot := len + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedLiteralSymFast9 br =
      some (sym,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
          (by
            have hk : len ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot len hbit)) := by
  have hsym : 257 ≤ (fixedLenMatchInfo matchLen).1 ∧ (fixedLenMatchInfo matchLen).1 ≤ 285 := by
    have h := fixedLenMatchInfo_spec_get! matchLen hlen.1 hlen.2
    exact ⟨h.1, h.2.1⟩
  simpa using
    (decodeFixedLiteralSymFast9_readerAt_writeBits_matchSym (bw := bw)
      (sym := (fixedLenMatchInfo matchLen).1) (restBits := restBits) (restLen := restLen)
      (hsym := hsym) (hrest2 := hrest2) (hbit := hbit) (hcur := hcur))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_succ_of_some
    (fuel : Nat) (br : BitReader) (out : ByteArray) (res : BitReader × ByteArray)
    (h : decodeFixedBlockFuelFast fuel br out = some res) :
    decodeFixedBlockFuelFast (fuel + 1) br out = some res := by
  induction fuel generalizing br out res with
  | zero =>
      simpa [decodeFixedBlockFuelFast] using h
  | succ fuel ih =>
      cases hsym : decodeFixedLiteralSymFast9 br with
      | none =>
          simp [decodeFixedBlockFuelFast.eq_2, hsym] at h
      | some symBr =>
          cases symBr with
          | mk sym br' =>
              by_cases hlit : sym < 256
              · have hrec : decodeFixedBlockFuelFast fuel br' (out.push (u8 sym)) = some res := by
                  simpa [decodeFixedBlockFuelFast.eq_2, hsym, hlit] using h
                calc
                  decodeFixedBlockFuelFast (fuel + 1 + 1) br out
                      = decodeFixedBlockFuelFast (fuel + 1) br' (out.push (u8 sym)) := by
                          simpa [Nat.add_assoc] using
                            (decodeFixedBlockFuelFast_step_literal_of_decodes
                              (fuel := fuel + 1) (br := br) (br' := br') (out := out) (sym := sym)
                              (hdecodeSym := hsym) (hlit := hlit))
                  _ = some res := ih _ _ _ hrec
              · cases heob : (sym == 256) with
                | true =>
                    have hs : sym = 256 := by
                      simpa using heob
                    have hres : (br', out) = res := by
                      simpa [decodeFixedBlockFuelFast.eq_2, hsym, hlit, heob, hs] using h
                    calc
                      decodeFixedBlockFuelFast (fuel + 1 + 1) br out = some (br', out) := by
                        simpa [Nat.add_assoc] using
                          (decodeFixedBlockFuelFast_step_eob_of_decodes
                            (fuel := fuel + 1) (br := br) (br' := br') (out := out) (sym := sym)
                            (hdecodeSym := hsym) (hnotLit := hlit) (heob := heob))
                      _ = some res := by cases hres; rfl
                | false =>
                    have hs : sym ≠ 256 := by
                      intro hs
                      simpa [hs] using heob
                    by_cases hlen : 257 ≤ sym ∧ sym ≤ 285
                    · let extra :=
                        Array.getInternal lengthExtra (sym - 257) (by
                          have hidxle : sym - 257 ≤ 28 := by
                            omega
                          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                          have hsize : lengthExtra.size = 29 := by decide
                          simpa [hsize] using hidxlt)
                      by_cases hbits : br'.bitIndex + extra ≤ br'.data.size * 8
                      · let lenBr := decodeLength sym br' hlen (by simpa using hbits)
                        let len := lenBr.1
                        let br'' := lenBr.2
                        cases hdistSym : decodeFixedDistanceSym br'' with
                        | none =>
                            simp [decodeFixedBlockFuelFast.eq_2, hsym, hlit, heob, hlen,
                              hs, extra, hbits, lenBr, len, br'', hdistSym] at h
                        | some distPair =>
                            cases distPair with
                            | mk distSym br''' =>
                                by_cases hdist : distSym < distBases.size
                                · let extraD :=
                                    Array.getInternal distExtra distSym (by
                                      have hDistExtraSize : distExtra.size = 30 := by decide
                                      have hDistBasesSize : distBases.size = 30 := by decide
                                      simpa [hDistExtraSize, hDistBasesSize] using hdist)
                                  by_cases hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8
                                  · let distBr := decodeDistance distSym br''' hdist (by simpa using hbitsD)
                                    let distance := distBr.1
                                    let br'''' := distBr.2
                                    cases hcopy : copyDistance out distance len with
                                    | none =>
                                        simp [decodeFixedBlockFuelFast.eq_2, hsym, hlit, heob, hlen,
                                          hs, extra, hbits, lenBr, len, br'', hdistSym, hdist, extraD, hbitsD,
                                          distBr, distance, br'''', hcopy] at h
                                    | some out' =>
                                        have hdecodeLen :
                                            decodeLength sym br' hlen (by simpa [extra] using hbits) =
                                              (len, br'') := by
                                          simp [lenBr, len, br'']
                                        have hdecodeDist :
                                            decodeDistance distSym br''' hdist
                                              (by simpa [extraD] using hbitsD) = (distance, br'''') := by
                                          simp [distBr, distance, br'''']
                                        have hrecAll :
                                            br'.bitIndex + extra ≤ br'.data.size * 8 ∧
                                              br'''.bitIndex + extraD ≤ br'''.data.size * 8 ∧
                                              decodeFixedBlockFuelFast fuel br'''' out' = some res := by
                                          simpa [decodeFixedBlockFuelFast.eq_2, hsym, hlit, heob, hlen,
                                            hs, extra, hbits, hdecodeLen, hdistSym, hdist, extraD, hbitsD,
                                            hdecodeDist, hcopy] using h
                                        have hrec : decodeFixedBlockFuelFast fuel br'''' out' = some res := by
                                          exact hrecAll.2.2
                                        calc
                                          decodeFixedBlockFuelFast (fuel + 1 + 1) br out
                                              = decodeFixedBlockFuelFast (fuel + 1) br'''' out' := by
                                                  simpa [Nat.add_assoc, extra, extraD, lenBr, len, br'', distBr,
                                                    distance, br''''] using
                                                    (decodeFixedBlockFuelFast_step_match_of_decodes
                                                      (fuel := fuel + 1) (br := br) (br' := br')
                                                      (br'' := br'') (br''' := br''') (br'''' := br'''')
                                                      (out := out) (out' := out') (sym := sym) (extra := extra)
                                                      (len := len) (distSym := distSym) (extraD := extraD)
                                                      (distance := distance) (hdecodeSym := hsym)
                                                      (hnotLit := hlit) (hnotEob := heob) (hsym := hlen)
                                                      (hextra := rfl) (hbits := by simpa [extra] using hbits)
                                                      (hdecodeLen := hdecodeLen)
                                                      (hdecodeDistSym := hdistSym) (hdist := hdist)
                                                      (hextraD := rfl)
                                                      (hbitsD := by simpa [extraD] using hbitsD)
                                                      (hdecodeDist := hdecodeDist) (hcopy := hcopy))
                                          _ = some res := ih _ _ _ hrec
                                  · have hbitsDFalse :
                                        ¬ br'''.bitIndex +
                                            distExtra[distSym]'(by
                                              have hDistExtraSize : distExtra.size = 30 := by decide
                                              have hDistBasesSize : distBases.size = 30 := by decide
                                              simpa [hDistExtraSize, hDistBasesSize] using hdist) ≤
                                              br'''.data.size * 8 := by
                                      simpa [extraD] using hbitsD
                                    simp [decodeFixedBlockFuelFast.eq_2, hsym, hlit, heob, hlen,
                                      hs, hbitsDFalse, extra, hbits, lenBr, len, br'', hdistSym, hdist] at h
                                · simp [decodeFixedBlockFuelFast.eq_2, hsym, hlit, heob, hlen,
                                      hs, extra, hbits, lenBr, len, br'', hdistSym, hdist] at h
                      · have hbitsFalse :
                            ¬ br'.bitIndex +
                                lengthExtra[sym - 257]'(by
                                  have hidxle : sym - 257 ≤ 28 := by
                                    omega
                                  have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                                  have hsize : lengthExtra.size = 29 := by decide
                                  simpa [hsize] using hidxlt) ≤ br'.data.size * 8 := by
                          simpa [extra] using hbits
                        simp [decodeFixedBlockFuelFast.eq_2, hsym, hlit, heob, hlen, hs, hbitsFalse] at h
                    · simp [decodeFixedBlockFuelFast.eq_2, hsym, hlit, heob, hlen, hs] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_add_of_some
    (fuel extra : Nat) (br : BitReader) (out : ByteArray) (res : BitReader × ByteArray)
    (h : decodeFixedBlockFuelFast fuel br out = some res) :
    decodeFixedBlockFuelFast (fuel + extra) br out = some res := by
  induction extra generalizing fuel br out res with
  | zero =>
      simpa using h
  | succ extra ih =>
      have hbase : decodeFixedBlockFuelFast (fuel + extra) br out = some res := by
        exact ih (fuel := fuel) (br := br) (out := out) (res := res) h
      simpa [Nat.add_assoc] using
        (decodeFixedBlockFuelFast_succ_of_some
          (fuel := fuel + extra) (br := br) (out := out) (res := res) hbase)

set_option maxRecDepth 100000 in
lemma decodeLength_fixedLenMatchInfo_readerAt_writeBits_prefix_exists
    (bw : BitWriter) (matchLen restBits restLen : Nat)
    (hlen : 3 ≤ matchLen ∧ matchLen ≤ 258)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let info := fixedLenMatchInfo matchLen
    let sym := info.1
    let extraBits := info.2.1
    let extraLen := info.2.2
    let bitsTot := extraBits ||| (restBits <<< extraLen)
    let lenTot := extraLen + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    ∃ hsym hbits,
      decodeLength sym br hsym hbits =
        (matchLen,
          BitWriter.readerAt (BitWriter.writeBits bw bitsTot extraLen) bw'.flush
            (by
              have hk : extraLen ≤ lenTot := by omega
              simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot extraLen lenTot hk))
            (bitPos_lt_8_writeBits bw bitsTot extraLen hbit)) := by
  have hspec :
      let info := fixedLenMatchInfo matchLen
      let sym := info.1
      let extraBits := info.2.1
      let extraLen := info.2.2
      ∃ hsym : 257 ≤ sym ∧ sym ≤ 285,
        ∃ hidxBase : sym - 257 < lengthBases.size,
          ∃ hidxExtra : sym - 257 < lengthExtra.size,
            extraLen = Array.getInternal lengthExtra (sym - 257) hidxExtra ∧
            Array.getInternal lengthBases (sym - 257) hidxBase + extraBits = matchLen ∧
            extraBits < 2 ^ extraLen := by
    simpa using fixedLenMatchInfo_spec_internal matchLen hlen.1 hlen.2
  rcases hspec with ⟨hsym, hidxBase, hidxExtra, hextra, hbase, hbitsLt⟩
  let info := fixedLenMatchInfo matchLen
  let sym := info.1
  let extraBits := info.2.1
  let extraLen := info.2.2
  let bitsTot := extraBits ||| (restBits <<< extraLen)
  let lenTot := extraLen + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  have hcanonExtra :
      lengthExtra[sym - 257]'(by
        have hidxlt : sym - 257 < lengthExtra.size := hidxExtra
        have hsize : lengthExtra.size = 29 := by decide
        simpa [hsize] using hidxlt) = extraLen := by
    have hidx' : sym - 257 < lengthExtra.size := by
      have hidxlt : sym - 257 < lengthExtra.size := hidxExtra
      exact hidxlt
    have hprf : hidx' =
        (by
          have hidxlt : sym - 257 < lengthExtra.size := hidxExtra
          have hsize : lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt) := Subsingleton.elim _ _
    calc
      lengthExtra[sym - 257]'(by
        have hidxlt : sym - 257 < lengthExtra.size := hidxExtra
        have hsize : lengthExtra.size = 29 := by decide
        simpa [hsize] using hidxlt)
          = Array.getInternal lengthExtra (sym - 257) hidx' := by
              simp [Array.getInternal, getElem!_pos, hprf]
      _ = Array.getInternal lengthExtra (sym - 257) hidxExtra := by
            simpa [hidx'] using congrArg (fun h => Array.getInternal lengthExtra (sym - 257) h) hprf.symm
      _ = extraLen := by simpa using hextra.symm
  have hread : br.bitIndex +
      lengthExtra[sym - 257]'(by
        have hidxlt : sym - 257 < lengthExtra.size := hidxExtra
        have hsize : lengthExtra.size = 29 := by decide
        simpa [hsize] using hidxlt) ≤ br.data.size * 8 := by
    have h :=
      readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := extraLen)
        (hk := Nat.le_add_right extraLen restLen) (hbit := hbit)
    simpa [br, bw', lenTot, hcanonExtra] using h
  refine ⟨hsym, hread, ?_⟩
  simpa [br, bw', bitsTot, lenTot] using
    (decodeLength_readerAt_writeBits_prefix (bw := bw) (sym := sym) (extraBits := extraBits)
      (extraLen := extraLen) (restBits := restBits) (restLen := restLen) (lenOut := matchLen)
      (hsym := hsym) (hidxBase := hidxBase) (hidxExtra := hidxExtra)
      (hextra := hextra) (hbase := hbase) (hbitsLt := hbitsLt) (hbit := hbit) (hcur := hcur))

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_fixedLenMatchInfo_dist1_of_decodes
    (fuel : Nat) (br0 br1 br2 brAfter : BitReader) (out : ByteArray) (matchLen : Nat)
    (_hlen : 3 ≤ matchLen ∧ matchLen ≤ 258)
    (hdecodeSym :
      decodeFixedLiteralSymFast9 br0 = some ((fixedLenMatchInfo matchLen).1, br1))
    (hdecodeLenEx :
      ∃ hsym hbits0, decodeLength (fixedLenMatchInfo matchLen).1 br1 hsym hbits0 = (matchLen, br2))
    (hdecodeDistEx :
      ∃ hdist hbitsD0, decodeFixedDistanceSym br2 = some (0, brAfter) ∧
        decodeDistance 0 brAfter hdist hbitsD0 = (1, brAfter))
    (hcopy :
      copyDistance out 1 matchLen = some (pushRepeat out (out.get! (out.size - 1)) matchLen)) :
    decodeFixedBlockFuelFast (fuel + 1) br0 out =
      decodeFixedBlockFuelFast fuel brAfter (pushRepeat out (out.get! (out.size - 1)) matchLen) := by
  let sym := (fixedLenMatchInfo matchLen).1
  rcases hdecodeLenEx with ⟨hsymLen, hbitsLen0, hdecodeLen0⟩
  rcases hdecodeDistEx with ⟨hdist0, hbitsD0, hdecodeDistSym, hdecodeDist0⟩
  let extra :=
    lengthExtra[sym - 257]'(by
      have hidxle : sym - 257 ≤ 28 := by
        have hs := hsymLen
        omega
      have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
      have hsize : lengthExtra.size = 29 := by decide
      simpa [hsize] using hidxlt)
  let extraD :=
    distExtra[0]'(by
      have hDistExtraSize : distExtra.size = 30 := by decide
      have hDistBasesSize : distBases.size = 30 := by decide
      simpa [hDistExtraSize, hDistBasesSize] using hdist0)
  have hnotLit : ¬ sym < 256 := by
    have hs := hsymLen
    omega
  have hnotEob : (sym == 256) = false := by
    cases hbeq : (sym == 256) with
    | false => simpa using hbeq
    | true =>
        have hs : sym = 256 := by simpa [sym] using hbeq
        omega
  have hbitsLen : br1.bitIndex + extra ≤ br1.data.size * 8 := by
    simpa [extra] using hbitsLen0
  have hextra :
      extra = Array.getInternal lengthExtra (sym - 257) (by
        have hidxle : sym - 257 ≤ 28 := by
          have hs := hsymLen
          omega
        have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
        have hsize : lengthExtra.size = 29 := by decide
        simpa [hsize] using hidxlt) := by
    simp [extra, Array.getInternal, getElem!_pos]
  have hbitsLenCanon :
      br1.bitIndex +
        lengthExtra[sym - 257]'(by
          have hidxle : sym - 257 ≤ 28 := by
            have hs := hsymLen
            omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt) ≤ br1.data.size * 8 := by
    simpa [extra] using hbitsLen
  have hdecodeLen :
      decodeLength sym br1 hsymLen
        (by
          have hbits' :
              br1.bitIndex +
                lengthExtra[sym - 257]'(by
                  have hidxle : sym - 257 ≤ 28 := by
                    have hs := hsymLen
                    omega
                  have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                  have hsize : lengthExtra.size = 29 := by decide
                  simpa [hsize] using hidxlt) ≤ br1.data.size * 8 := by
            simpa [hextra] using hbitsLen
          simpa using hbits') = (matchLen, br2) := by
    have hArgEq : hbitsLenCanon = hbitsLen0 := Subsingleton.elim _ _
    simpa [sym, hArgEq] using hdecodeLen0
  have hbitsD : brAfter.bitIndex + extraD ≤ brAfter.data.size * 8 := by
    simpa [extraD] using hbitsD0
  have hextraD :
      extraD = Array.getInternal distExtra 0 (by
        have hDistExtraSize : distExtra.size = 30 := by decide
        have hDistBasesSize : distBases.size = 30 := by decide
        simpa [hDistExtraSize, hDistBasesSize] using hdist0) := by
    simp [extraD, Array.getInternal, getElem!_pos]
  have hbitsDistCanon :
      brAfter.bitIndex +
        distExtra[0]'(by
          have hDistExtraSize : distExtra.size = 30 := by decide
          have hDistBasesSize : distBases.size = 30 := by decide
          simpa [hDistExtraSize, hDistBasesSize] using hdist0) ≤ brAfter.data.size * 8 := by
    simpa [extraD] using hbitsD
  have hdecodeDist :
      decodeDistance 0 brAfter hdist0
        (by
          have hbitsD' :
              brAfter.bitIndex +
                distExtra[0]'(by
                  have hDistExtraSize : distExtra.size = 30 := by decide
                  have hDistBasesSize : distBases.size = 30 := by decide
                  simpa [hDistExtraSize, hDistBasesSize] using hdist0) ≤ brAfter.data.size * 8 := by
            simpa [hextraD] using hbitsD
          simpa using hbitsD') = (1, brAfter) := by
    have hArgEq : hbitsDistCanon = hbitsD0 := Subsingleton.elim _ _
    simpa [hArgEq] using hdecodeDist0
  exact
    (decodeFixedBlockFuelFast_step_match_of_decodes
      (fuel := fuel) (br := br0) (br' := br1) (br'' := br2) (br''' := brAfter) (br'''' := brAfter)
      (out := out) (out' := pushRepeat out (out.get! (out.size - 1)) matchLen)
      (sym := sym) (extra := extra) (len := matchLen) (distSym := 0) (extraD := extraD) (distance := 1)
      (hdecodeSym := by simpa [sym] using hdecodeSym)
      (hnotLit := hnotLit) (hnotEob := hnotEob) (hsym := hsymLen)
      (hextra := hextra) (hbits := hbitsLen) (hdecodeLen := hdecodeLen)
      (hdecodeDistSym := hdecodeDistSym) (hdist := hdist0) (hextraD := hextraD)
      (hbitsD := hbitsD) (hdecodeDist := hdecodeDist) (hcopy := hcopy))

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_fixedLenMatchInfo_dist1_afterSym_readerAt_writeBits
    (fuel : Nat) (br0 : BitReader) (bw1 : BitWriter) (matchLen tailBits tailLen : Nat)
    (out : ByteArray) (hlen : 3 ≤ matchLen ∧ matchLen ≤ 258) (hout : 0 < out.size)
    (hbit1 : bw1.bitPos < 8) (hcur1 : bw1.curClearAbove) :
    let info := fixedLenMatchInfo matchLen
    let sym := info.1
    let extraBits := info.2.1
    let extraLen := info.2.2
    let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
    let distLenTot := 5 + tailLen
    let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
    let lenLenTot := extraLen + distLenTot
    let bwLenAll := BitWriter.writeBits bw1 lenBitsTot lenLenTot
    let br1 := BitWriter.readerAt bw1 bwLenAll.flush (flush_size_writeBits_le bw1 lenBitsTot lenLenTot) hbit1
    decodeFixedLiteralSymFast9 br0 = some (sym, br1) →
      let bw2 := BitWriter.writeBits bw1 lenBitsTot extraLen
      let bwDistAll := BitWriter.writeBits bw2 distBitsTot distLenTot
      let brAfter := BitWriter.readerAt (BitWriter.writeBits bw2 distBitsTot 5) bwDistAll.flush
        (by
          have hk : 5 ≤ distLenTot := by omega
          simpa [distLenTot] using (flush_size_writeBits_prefix bw2 distBitsTot 5 distLenTot hk))
        (bitPos_lt_8_writeBits bw2 distBitsTot 5 (bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1))
      decodeFixedBlockFuelFast (fuel + 1) br0 out =
        decodeFixedBlockFuelFast fuel brAfter (pushRepeat out (out.get! (out.size - 1)) matchLen) := by
  let info := fixedLenMatchInfo matchLen
  let sym := info.1
  let extraBits := info.2.1
  let extraLen := info.2.2
  let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
  let distLenTot := 5 + tailLen
  let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
  let lenLenTot := extraLen + distLenTot
  let bwLenAll := BitWriter.writeBits bw1 lenBitsTot lenLenTot
  let br1 := BitWriter.readerAt bw1 bwLenAll.flush (flush_size_writeBits_le bw1 lenBitsTot lenLenTot) hbit1
  change decodeFixedLiteralSymFast9 br0 = some (sym, br1) → _
  intro hdecodeSym0
  let bw2 := BitWriter.writeBits bw1 lenBitsTot extraLen
  let bwDistAll := BitWriter.writeBits bw2 distBitsTot distLenTot
  let brAfter := BitWriter.readerAt (BitWriter.writeBits bw2 distBitsTot 5) bwDistAll.flush
    (by
      have hk : 5 ≤ distLenTot := by omega
      simpa [distLenTot] using (flush_size_writeBits_prefix bw2 distBitsTot 5 distLenTot hk))
    (bitPos_lt_8_writeBits bw2 distBitsTot 5 (bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1))
  have hspecInternal :
      let info := fixedLenMatchInfo matchLen
      let sym := info.1
      let extraBits := info.2.1
      let extraLen := info.2.2
      ∃ hsym : 257 ≤ sym ∧ sym ≤ 285,
        ∃ hidxBase : sym - 257 < lengthBases.size,
          ∃ hidxExtra : sym - 257 < lengthExtra.size,
            extraLen = Array.getInternal lengthExtra (sym - 257) hidxExtra ∧
            Array.getInternal lengthBases (sym - 257) hidxBase + extraBits = matchLen ∧
            extraBits < 2 ^ extraLen := by
    simpa [info, sym, extraBits, extraLen] using
      fixedLenMatchInfo_spec_internal matchLen hlen.1 hlen.2
  rcases hspecInternal with ⟨_, _, _, _, _, hbitsLtExtra⟩
  have hmodLen : lenBitsTot % 2 ^ extraLen = extraBits := by
    have hmod' := mod_two_pow_or_shift extraBits distBitsTot extraLen extraLen (by exact le_rfl)
    have hbitsMod : extraBits % 2 ^ extraLen = extraBits := Nat.mod_eq_of_lt hbitsLtExtra
    simpa [lenBitsTot, hbitsMod] using hmod'
  have hwriteLenPrefix : BitWriter.writeBits bw1 lenBitsTot extraLen = BitWriter.writeBits bw1 extraBits extraLen := by
    calc
      BitWriter.writeBits bw1 lenBitsTot extraLen = BitWriter.writeBits bw1 (lenBitsTot % 2 ^ extraLen) extraLen := by
        simpa using (writeBits_mod bw1 lenBitsTot extraLen)
      _ = BitWriter.writeBits bw1 extraBits extraLen := by
        simp [hmodLen]
  have hconcatLen :
      BitWriter.writeBits bw1 lenBitsTot lenLenTot = BitWriter.writeBits bw2 distBitsTot distLenTot := by
    calc
      BitWriter.writeBits bw1 lenBitsTot lenLenTot =
          BitWriter.writeBits (BitWriter.writeBits bw1 extraBits extraLen) distBitsTot distLenTot := by
        simpa [lenBitsTot, lenLenTot] using
          (writeBits_concat bw1 extraBits distBitsTot extraLen distLenTot hbitsLtExtra)
      _ = BitWriter.writeBits bw2 distBitsTot distLenTot := by
          simp [bw2, hwriteLenPrefix]
  let br2 := BitWriter.readerAt bw2 bwLenAll.flush
    (by
      have hk : extraLen ≤ lenLenTot := by omega
      simpa [bwLenAll, lenLenTot] using
        (flush_size_writeBits_prefix bw1 lenBitsTot extraLen lenLenTot hk))
    (bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1)
  have hdecodeLenEx' :=
    decodeLength_fixedLenMatchInfo_readerAt_writeBits_prefix_exists
      (bw := bw1) (matchLen := matchLen) (restBits := distBitsTot) (restLen := distLenTot)
      (hlen := hlen) (hbit := hbit1) (hcur := hcur1)
  have hdecodeLenEx :
      ∃ hsym hbits0, decodeLength sym br1 hsym hbits0 = (matchLen, br2) := by
    rcases hdecodeLenEx' with ⟨hsymLen, hbitsLen0, hdecodeLen0⟩
    have hdecodeLen0a :
        decodeLength sym br1 hsymLen hbitsLen0 =
          (matchLen,
            BitWriter.readerAt bw2 bwLenAll.flush
              (by
                have hk : extraLen ≤ lenLenTot := by omega
                simpa [bwLenAll, lenLenTot] using
                  (flush_size_writeBits_prefix bw1 lenBitsTot extraLen lenLenTot hk))
              (bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1)) := by
      simpa [sym, br1, bwLenAll, bw2] using hdecodeLen0
    refine ⟨hsymLen, hbitsLen0, ?_⟩
    simpa [br2] using hdecodeLen0a
  have hdistTriple :=
    decodeFixedDistanceSym_zero_decodeDistance_zero_copyDistance_one_exists
      (bw := bw2) (restBits := tailBits) (restLen := tailLen) (matchLen := matchLen) (out := out)
      (hout := hout) (hbit := bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1)
      (hcur := curClearAbove_writeBits bw1 lenBitsTot extraLen hbit1 hcur1)
  let br2Dist := BitWriter.readerAt bw2 bwDistAll.flush
    (by
      have hk : extraLen ≤ lenLenTot := by omega
      simpa [bwDistAll, hconcatLen, lenLenTot] using
        (flush_size_writeBits_prefix bw1 lenBitsTot extraLen lenLenTot hk))
    (bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1)
  have hbwEq : bwLenAll = bwDistAll := by
    simpa [bwLenAll, bwDistAll] using hconcatLen
  have hbr2Eq : br2 = br2Dist := by
    have hdata : br2.data = br2Dist.data := by
      simpa [br2, br2Dist, BitWriter.readerAt] using congrArg BitWriter.flush hbwEq
    have hbyte : br2.bytePos = br2Dist.bytePos := by
      simp [br2, br2Dist, BitWriter.readerAt]
    have hbit : br2.bitPos = br2Dist.bitPos := by
      simp [br2, br2Dist, BitWriter.readerAt]
    exact BitReader.ext hdata hbyte hbit
  have hdecodeDistEx :
      ∃ hdist hbitsD0, decodeFixedDistanceSym br2 = some (0, brAfter) ∧
        decodeDistance 0 brAfter hdist hbitsD0 = (1, brAfter) := by
    rcases hdistTriple with ⟨hdist0, hbitsD0, hdecodeDistSym0, hdecodeDist0, _hcopy0⟩
    have hdecodeDistSym0' : decodeFixedDistanceSym br2Dist = some (0, brAfter) := by
      simpa [br2Dist, brAfter, bwDistAll, distLenTot, distBitsTot] using hdecodeDistSym0
    refine ⟨hdist0, hbitsD0, ?_, ?_⟩
    · simpa [hbr2Eq] using hdecodeDistSym0'
    · change decodeDistance 0 brAfter hdist0 hbitsD0 = (1, brAfter)
      exact hdecodeDist0
  have hcopy0 :
      copyDistance out 1 matchLen = some (pushRepeat out (out.get! (out.size - 1)) matchLen) := by
    rcases hdistTriple with ⟨_, _, _, _, hcopy0⟩
    exact hcopy0
  simpa [info, sym, extraBits, extraLen, distBitsTot, distLenTot, lenBitsTot, lenLenTot,
    bwLenAll, br1, bw2, bwDistAll, br2, brAfter, br2Dist, hbwEq, hbr2Eq] using
    (decodeFixedBlockFuelFast_step_fixedLenMatchInfo_dist1_of_decodes
      (fuel := fuel) (br0 := br0) (br1 := br1) (br2 := br2) (brAfter := brAfter)
      (out := out) (matchLen := matchLen) (_hlen := hlen)
      (hdecodeSym := by simpa [sym] using hdecodeSym0)
      (hdecodeLenEx := hdecodeLenEx) (hdecodeDistEx := hdecodeDistEx) (hcopy := hcopy0))

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_fixedLenMatchInfo_dist1_readerAt_writeBits
    (fuel : Nat) (bw : BitWriter) (matchLen tailBits tailLen : Nat) (out : ByteArray)
    (hlen : 3 ≤ matchLen ∧ matchLen ≤ 258) (hout : 0 < out.size)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let info := fixedLenMatchInfo matchLen
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
      decodeFixedBlockFuelFast fuel brAfter (pushRepeat out (out.get! (out.size - 1)) matchLen) := by
  let info := fixedLenMatchInfo matchLen
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
  let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
  have hbit1 : bw1.bitPos < 8 := by
    exact bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit
  have hcur1 : bw1.curClearAbove := by
    exact curClearAbove_writeBits bw bitsTot codeLen.2 hbit hcur
  have hrest2 : 2 ≤ lenLenTot := by
    omega
  have hdecodeSym0 :
      decodeFixedLiteralSymFast9 br0 =
        some (sym,
          BitWriter.readerAt bw1 bwAll.flush
            (by
              have hk : codeLen.2 ≤ lenTot := by omega
              simpa [bwAll, lenTot] using
                (flush_size_writeBits_prefix bw bitsTot codeLen.2 lenTot hk))
            hbit1) := by
    simpa [info, sym, extraBits, extraLen, codeLen, symBits, distBitsTot, distLenTot, lenBitsTot,
      lenLenTot, bitsTot, lenTot, bwAll, br0, bw1, hbit1] using
      (decodeFixedLiteralSymFast9_readerAt_writeBits_fixedLenMatchInfo
        (bw := bw) (matchLen := matchLen) (restBits := lenBitsTot) (restLen := lenLenTot)
        (hlen := hlen) (hrest2 := hrest2) (hbit := hbit) (hcur := hcur))
  have hsymMatch : 257 ≤ sym ∧ sym ≤ 285 := by
    have h := fixedLenMatchInfo_spec_get! matchLen hlen.1 hlen.2
    exact ⟨h.1, h.2.1⟩
  have hsymBitsLt : symBits < 2 ^ codeLen.2 := by
    simpa [symBits] using (reverseBits_lt codeLen.1 codeLen.2)
  have hmodSym : bitsTot % 2 ^ codeLen.2 = symBits := by
    have hmod' := mod_two_pow_or_shift symBits lenBitsTot codeLen.2 codeLen.2 (by exact le_rfl)
    have hmodBits : symBits % 2 ^ codeLen.2 = symBits := Nat.mod_eq_of_lt hsymBitsLt
    simpa [bitsTot, hmodBits] using hmod'
  have hwriteSymPrefix : BitWriter.writeBits bw bitsTot codeLen.2 = BitWriter.writeBits bw symBits codeLen.2 := by
    calc
      BitWriter.writeBits bw bitsTot codeLen.2 = BitWriter.writeBits bw (bitsTot % 2 ^ codeLen.2) codeLen.2 := by
        simpa using (writeBits_mod bw bitsTot codeLen.2)
      _ = BitWriter.writeBits bw symBits codeLen.2 := by
        simp [hmodSym]
  have hconcatSym : BitWriter.writeBits bw bitsTot lenTot = BitWriter.writeBits bw1 lenBitsTot lenLenTot := by
    calc
      BitWriter.writeBits bw bitsTot lenTot = BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) lenBitsTot lenLenTot := by
        simpa [bitsTot, lenTot] using
          (writeBits_concat bw symBits lenBitsTot codeLen.2 lenLenTot hsymBitsLt)
      _ = BitWriter.writeBits bw1 lenBitsTot lenLenTot := by
        simp [bw1, hwriteSymPrefix]
  have hdecodeSym1 :
      decodeFixedLiteralSymFast9 br0 =
        some (sym,
          BitWriter.readerAt bw1 (BitWriter.writeBits bw1 lenBitsTot lenLenTot).flush
            (flush_size_writeBits_le bw1 lenBitsTot lenLenTot) hbit1) := by
    simpa [bwAll, hconcatSym, lenTot] using hdecodeSym0
  have hstep :=
    decodeFixedBlockFuelFast_step_fixedLenMatchInfo_dist1_afterSym_readerAt_writeBits
      (fuel := fuel) (br0 := br0) (bw1 := bw1) (matchLen := matchLen) (tailBits := tailBits)
      (tailLen := tailLen) (out := out) (hlen := hlen) (hout := hout) (hbit1 := hbit1) (hcur1 := hcur1)
  have hstep' := hstep hdecodeSym1
  simpa [info, sym, extraBits, extraLen, codeLen, symBits, distBitsTot, distLenTot, lenBitsTot, lenLenTot,
    bitsTot, lenTot, bwAll, br0, bw1] using hstep'

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_step_chooseFixedMatchChunkLen_dist1_readerAt_writeBits
    (fuel : Nat) (bw : BitWriter) (remaining tailBits tailLen : Nat) (out : ByteArray)
    (hrem : 3 ≤ remaining) (hout : 0 < out.size)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let chunk := chooseFixedMatchChunkLen remaining
    let info := fixedLenMatchInfo chunk
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
      decodeFixedBlockFuelFast fuel brAfter (pushRepeat out (out.get! (out.size - 1)) chunk) := by
  let chunk := chooseFixedMatchChunkLen remaining
  have hbounds := chooseFixedMatchChunkLen_bounds remaining hrem
  have hlen : 3 ≤ chunk ∧ chunk ≤ 258 := ⟨hbounds.1, hbounds.2.1⟩
  simpa [chunk] using
    (decodeFixedBlockFuelFast_step_fixedLenMatchInfo_dist1_readerAt_writeBits
      (fuel := fuel) (bw := bw) (matchLen := chunk) (tailBits := tailBits) (tailLen := tailLen)
      (out := out) (hlen := hlen) (hout := hout) (hbit := hbit) (hcur := hcur))

set_option maxRecDepth 200000 in
lemma decodeFixedBlockFuelFast_dist1ChunkLoopBitsTail_readerAt_writeBits_exists'
    (fuel : Nat) (bw : BitWriter) (remaining tailBits tailLen bitsTot0 lenTot0 : Nat) (out : ByteArray)
    (hout : 0 < out.size) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    (hbits : dist1ChunkLoopBitsTail remaining tailBits tailLen = (bitsTot0, lenTot0)) :
    ∃ brAfter,
      decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining)
        (BitWriter.readerAt bw (BitWriter.writeBits bw bitsTot0 lenTot0).flush
          (flush_size_writeBits_le bw bitsTot0 lenTot0) hbit) out =
        decodeFixedBlockFuelFast fuel brAfter (dist1ChunkLoopOut out remaining) := by
  revert fuel bw tailBits tailLen bitsTot0 lenTot0 out hout hbit hcur hbits
  refine Nat.strong_induction_on remaining ?_
  intro remaining ih fuel bw tailBits tailLen bitsTot0 lenTot0 out hout hbit hcur hbits
  by_cases hrem : 3 ≤ remaining
  · let chunk := chooseFixedMatchChunkLen remaining
    let rem' := remaining - chunk
    let rest := dist1ChunkLoopBitsTail rem' tailBits tailLen
    let tailBits' := rest.1
    let tailLen' := rest.2
    let info := fixedLenMatchInfo chunk
    let sym := info.1
    let extraBits := info.2.1
    let extraLen := info.2.2
    let codeLen := fixedLitLenCode sym
    let symBits := reverseBits codeLen.1 codeLen.2
    let distBitsTot := (0 : Nat) ||| (tailBits' <<< 5)
    let distLenTot := 5 + tailLen'
    let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
    let lenLenTot := extraLen + distLenTot
    let bitsTotL := symBits ||| (lenBitsTot <<< codeLen.2)
    let lenTotL := codeLen.2 + lenLenTot
    let bwAll := BitWriter.writeBits bw bitsTotL lenTotL
    let br0 := BitWriter.readerAt bw bwAll.flush (flush_size_writeBits_le bw bitsTotL lenTotL) hbit
    let bw1 := BitWriter.writeBits bw bitsTotL codeLen.2
    let bw2 := BitWriter.writeBits bw1 lenBitsTot extraLen
    let bwChunk := BitWriter.writeBits bw2 distBitsTot 5
    let bwDistAll := BitWriter.writeBits bw2 distBitsTot distLenTot
    let brAfter := BitWriter.readerAt bwChunk bwDistAll.flush
      (by
        have hk : 5 ≤ distLenTot := by omega
        simpa [bwChunk, distLenTot] using
          (flush_size_writeBits_prefix bw2 distBitsTot 5 distLenTot hk))
      (bitPos_lt_8_writeBits bw2 distBitsTot 5
        (bitPos_lt_8_writeBits bw1 lenBitsTot extraLen
          (bitPos_lt_8_writeBits bw bitsTotL codeLen.2 hbit)))
    have hchunkSub : rem' < remaining := by
      simpa [chunk, rem'] using (chooseFixedMatchChunkLen_sub_lt remaining hrem)
    have hbitsGeTail := dist1ChunkLoopBitsTail_of_ge3 remaining tailBits tailLen hrem
    have hpairFromBits :
        (bitsTotL, lenTotL) = (bitsTot0, lenTot0) := by
      calc
        (bitsTotL, lenTotL) = dist1ChunkLoopBitsTail remaining tailBits tailLen := by
          simpa [chunk, rem', rest, tailBits', tailLen', info, sym, extraBits, extraLen, codeLen, symBits,
            distBitsTot, distLenTot, lenBitsTot, lenLenTot, bitsTotL, lenTotL] using hbitsGeTail.symm
        _ = (bitsTot0, lenTot0) := hbits
    have hbitsEq : bitsTotL = bitsTot0 := by
      exact congrArg Prod.fst hpairFromBits
    have hlenEq : lenTotL = lenTot0 := by
      exact congrArg Prod.snd hpairFromBits
    have hout' : 0 < (pushRepeat out (out.get! (out.size - 1)) chunk).size := by
      dsimp [chunk]
      exact pushRepeat_pos out (out.get! (out.size - 1)) (chooseFixedMatchChunkLen remaining) hout
    have hstep :=
      decodeFixedBlockFuelFast_step_chooseFixedMatchChunkLen_dist1_readerAt_writeBits
        (fuel := fuel + dist1ChunkLoopSteps rem') (bw := bw) (remaining := remaining)
        (tailBits := tailBits') (tailLen := tailLen') (out := out)
        (hrem := hrem) (hout := hout) (hbit := hbit) (hcur := hcur)
    have hbit1 : bw1.bitPos < 8 := by
      exact bitPos_lt_8_writeBits bw bitsTotL codeLen.2 hbit
    have hbit2 : bw2.bitPos < 8 := by
      exact bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1
    have hcur1 : bw1.curClearAbove := by
      exact curClearAbove_writeBits bw bitsTotL codeLen.2 hbit hcur
    have hcur2 : bw2.curClearAbove := by
      exact curClearAbove_writeBits bw1 lenBitsTot extraLen hbit1 hcur1
    have hbitChunk : bwChunk.bitPos < 8 := by
      exact bitPos_lt_8_writeBits bw2 distBitsTot 5 hbit2
    have hcurChunk : bwChunk.curClearAbove := by
      exact curClearAbove_writeBits bw2 distBitsTot 5 hbit2 hcur2
    have hih :=
      ih rem' hchunkSub
        (fuel := fuel) (bw := bwChunk) (tailBits := tailBits) (tailLen := tailLen)
        (bitsTot0 := rest.1) (lenTot0 := rest.2)
        (out := pushRepeat out (out.get! (out.size - 1)) chunk)
        hout' hbitChunk hcurChunk (by rfl)
    rcases hih with ⟨brTail, hih⟩
    have hreader :
        brAfter =
          BitWriter.readerAt bwChunk (BitWriter.writeBits bwChunk tailBits' tailLen').flush
            (flush_size_writeBits_le bwChunk tailBits' tailLen') hbitChunk := by
      change
        BitWriter.readerAt bwChunk bwDistAll.flush
            (by
              have hk : 5 ≤ distLenTot := by omega
              simpa [bwChunk, distLenTot] using
                (flush_size_writeBits_prefix bw2 distBitsTot 5 distLenTot hk))
            hbitChunk
          =
        BitWriter.readerAt bwChunk (BitWriter.writeBits bwChunk tailBits' tailLen').flush
            (flush_size_writeBits_le bwChunk tailBits' tailLen') hbitChunk
      exact readerAt_writeBits_dist1Prefix_concat (bw2 := bw2) (tailBits := tailBits') (tailLen := tailLen')
        (hbit2 := hbit2)
    have hstepLocal :
        decodeFixedBlockFuelFast (fuel + (1 + dist1ChunkLoopSteps rem')) br0 out =
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem') brAfter
            (pushRepeat out (out.get! (out.size - 1)) chunk) := by
      simpa [chunk, rem', rest, tailBits', tailLen', info, sym, extraBits, extraLen, codeLen, symBits,
        distBitsTot, distLenTot, lenBitsTot, lenLenTot, bitsTotL, lenTotL, bwAll, br0, bw1, bw2, bwChunk,
        bwDistAll, brAfter, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
    have hbr0Eq :
        br0 =
          BitWriter.readerAt bw (BitWriter.writeBits bw bitsTot0 lenTot0).flush
            (flush_size_writeBits_le bw bitsTot0 lenTot0) hbit := by
      dsimp [br0, bwAll]
      simp [hbitsEq, hlenEq]
    have hstep' :
        decodeFixedBlockFuelFast (fuel + (1 + dist1ChunkLoopSteps rem'))
            (BitWriter.readerAt bw (BitWriter.writeBits bw bitsTot0 lenTot0).flush
              (flush_size_writeBits_le bw bitsTot0 lenTot0) hbit) out =
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem') brAfter
            (pushRepeat out (out.get! (out.size - 1)) chunk) := by
      simpa [hbr0Eq] using hstepLocal
    have hih' :
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem') brAfter
          (pushRepeat out (out.get! (out.size - 1)) chunk) =
        decodeFixedBlockFuelFast fuel brTail
          (dist1ChunkLoopOut (pushRepeat out (out.get! (out.size - 1)) chunk) rem') := by
      simpa [hreader] using hih
    refine ⟨brTail, ?_⟩
    have hstepsGe := dist1ChunkLoopSteps_of_ge3 remaining hrem
    have houtGe := dist1ChunkLoopOut_of_ge3 out remaining hrem
    have hmain := hstep'.trans hih'
    simpa [hstepsGe, houtGe, chunk, rem', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain
  · refine ⟨BitWriter.readerAt bw (BitWriter.writeBits bw tailBits tailLen).flush
      (flush_size_writeBits_le bw tailBits tailLen) hbit, ?_⟩
    have hbitsLt := dist1ChunkLoopBitsTail_of_lt3 remaining tailBits tailLen hrem
    have hstepsLt := dist1ChunkLoopSteps_of_lt3 remaining hrem
    have houtLt := dist1ChunkLoopOut_of_lt3 out remaining hrem
    have hpairParam :
        (bitsTot0, lenTot0) = (tailBits, tailLen) := by
      calc
        (bitsTot0, lenTot0) = dist1ChunkLoopBitsTail remaining tailBits tailLen := by
          simpa using hbits.symm
        _ = (tailBits, tailLen) := hbitsLt
    have hbitsEq : bitsTot0 = tailBits := by
      exact congrArg Prod.fst hpairParam
    have hlenEq : lenTot0 = tailLen := by
      exact congrArg Prod.snd hpairParam
    simpa [hbitsEq, hlenEq, hstepsLt, houtLt]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_dist1ChunkLoopBitsTail_readerAt_writeBits_exists
    (fuel : Nat) (bw : BitWriter) (remaining tailBits tailLen : Nat) (out : ByteArray)
    (hout : 0 < out.size) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    ∃ brAfter,
      decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining)
        (BitWriter.readerAt bw
          (BitWriter.writeBits bw
            (dist1ChunkLoopBitsTail remaining tailBits tailLen).1
            (dist1ChunkLoopBitsTail remaining tailBits tailLen).2).flush
          (flush_size_writeBits_le bw
            (dist1ChunkLoopBitsTail remaining tailBits tailLen).1
            (dist1ChunkLoopBitsTail remaining tailBits tailLen).2) hbit) out =
        decodeFixedBlockFuelFast fuel brAfter (dist1ChunkLoopOut out remaining) := by
  exact decodeFixedBlockFuelFast_dist1ChunkLoopBitsTail_readerAt_writeBits_exists'
    (fuel := fuel) (bw := bw) (remaining := remaining) (tailBits := tailBits) (tailLen := tailLen)
    (bitsTot0 := (dist1ChunkLoopBitsTail remaining tailBits tailLen).1)
    (lenTot0 := (dist1ChunkLoopBitsTail remaining tailBits tailLen).2)
    (out := out) (hout := hout) (hbit := hbit) (hcur := hcur) (hbits := rfl)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_dist1ChunkLoopTailLits_readerAt_writeBits_exists
    (fuel : Nat) (bw : BitWriter) (remaining tailBits tailLen : Nat)
    (out : ByteArray) (b : UInt8)
    (hout : 0 < out.size) (hlast : out.get! (out.size - 1) = b)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let remLit := dist1ChunkLoopRem remaining
    let litTail := literalRepeatBitsTail b remLit tailBits tailLen
    let bitsLen := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
    ∃ brAfter,
      decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit)
        (BitWriter.readerAt bw
          (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
          (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out =
        decodeFixedBlockFuelFast fuel brAfter (pushRepeat out b remaining) := by
  revert fuel bw tailBits tailLen out b hout hlast htail2 hbit hcur
  refine Nat.strong_induction_on remaining ?_
  intro remaining ih fuel bw tailBits tailLen out b hout hlast htail2 hbit hcur
  by_cases hrem : 3 ≤ remaining
  · let chunk := chooseFixedMatchChunkLen remaining
    let rem' := remaining - chunk
    let remLit := dist1ChunkLoopRem remaining
    let litTail := literalRepeatBitsTail b remLit tailBits tailLen
    let bitsLen := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
    have hremEq : remLit = dist1ChunkLoopRem rem' := by
      dsimp [remLit, rem']
      simpa [chunk] using (dist1ChunkLoopRem_of_ge3 remaining hrem)
    let restBits := dist1ChunkLoopBitsTail rem' litTail.1 litTail.2
    have hbitsGe := dist1ChunkLoopBitsTail_of_ge3 remaining litTail.1 litTail.2 hrem
    have hchunkBounds := chooseFixedMatchChunkLen_bounds remaining hrem
    have hchunkPos : 0 < chunk := by
      have : 3 ≤ chunk := by simpa [chunk] using hchunkBounds.1
      omega
    have hstep :=
      decodeFixedBlockFuelFast_step_chooseFixedMatchChunkLen_dist1_readerAt_writeBits
        (fuel := fuel + dist1ChunkLoopSteps rem' + remLit) (bw := bw)
        (remaining := remaining) (tailBits := restBits.1) (tailLen := restBits.2)
        (out := out) (hrem := hrem) (hout := hout) (hbit := hbit) (hcur := hcur)
    let chunkInfo := fixedLenMatchInfo chunk
    let sym := chunkInfo.1
    let extraBits := chunkInfo.2.1
    let extraLen := chunkInfo.2.2
    let codeLen := fixedLitLenCode sym
    let symBits := reverseBits codeLen.1 codeLen.2
    let distBitsTot := (0 : Nat) ||| (restBits.1 <<< 5)
    let distLenTot := 5 + restBits.2
    let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
    let lenLenTot := extraLen + distLenTot
    let bitsTot := symBits ||| (lenBitsTot <<< codeLen.2)
    let lenTot := codeLen.2 + lenLenTot
    let bwAll := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bwAll.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
    let bw2 := BitWriter.writeBits bw1 lenBitsTot extraLen
    let bwChunk := BitWriter.writeBits bw2 distBitsTot 5
    let bwDistAll := BitWriter.writeBits bw2 distBitsTot distLenTot
    let brAfterChunk := BitWriter.readerAt bwChunk bwDistAll.flush
      (by
        have hk : 5 ≤ distLenTot := by omega
        simpa [bwChunk, distLenTot] using (flush_size_writeBits_prefix bw2 distBitsTot 5 distLenTot hk))
      (bitPos_lt_8_writeBits bw2 distBitsTot 5
        (bitPos_lt_8_writeBits bw1 lenBitsTot extraLen
          (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit)))
    have hbitsPair :
        bitsLen = (bitsTot, lenTot) := by
      dsimp [bitsLen]
      simpa [chunk, rem', restBits, chunkInfo, sym, extraBits, extraLen, codeLen, symBits,
        distBitsTot, distLenTot, lenBitsTot, lenLenTot, bitsTot, lenTot] using hbitsGe
    have hbitsEq : bitsLen.1 = bitsTot := by
      exact congrArg Prod.fst hbitsPair
    have hlenEq : bitsLen.2 = lenTot := by
      exact congrArg Prod.snd hbitsPair
    have hstep' :
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit)
          (BitWriter.readerAt bw (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
            (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out =
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit)
          brAfterChunk (pushRepeat out b chunk) := by
      have hstepLocal :
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit + 1) br0 out =
            decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit)
              brAfterChunk (pushRepeat out (out.get! (out.size - 1)) chunk) := by
        simpa [chunk, restBits, chunkInfo, sym, extraBits, extraLen, codeLen, symBits, distBitsTot, distLenTot,
          lenBitsTot, lenLenTot, bitsTot, lenTot, bwAll, br0, bw1, bw2, bwChunk, bwDistAll, brAfterChunk,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
      have hstepsGe : dist1ChunkLoopSteps remaining = 1 + dist1ChunkLoopSteps rem' := by
        simpa [chunk, rem'] using (dist1ChunkLoopSteps_of_ge3 remaining hrem)
      have hpushLast :
          pushRepeat out (out.get! (out.size - 1)) chunk = pushRepeat out b chunk := by
        exact congrArg (fun x => pushRepeat out x chunk) hlast
      have hleft :
          BitWriter.readerAt bw (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
            (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit = br0 := by
        dsimp [br0]
        simp [hbitsEq, hlenEq, bwAll]
      have hright :
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit)
              brAfterChunk (pushRepeat out (out.get! (out.size - 1)) chunk) =
            decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit)
              brAfterChunk (pushRepeat out b chunk) := by
        simpa [hpushLast]
      calc
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit)
            (BitWriter.readerAt bw (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
              (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out
            = decodeFixedBlockFuelFast (fuel + (1 + dist1ChunkLoopSteps rem') + remLit)
                (BitWriter.readerAt bw (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
                  (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out := by
                  simp [hstepsGe, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = decodeFixedBlockFuelFast (fuel + (1 + dist1ChunkLoopSteps rem') + remLit) br0 out := by
              simp [hleft]
        _ = decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit)
              brAfterChunk (pushRepeat out (out.get! (out.size - 1)) chunk) := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstepLocal
        _ = decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit)
              brAfterChunk (pushRepeat out b chunk) := hright
    have hlt : rem' < remaining := by
      simpa [chunk, rem'] using (chooseFixedMatchChunkLen_sub_lt remaining hrem)
    have houtChunk : 0 < (pushRepeat out b chunk).size := by
      exact pushRepeat_pos out b chunk hout
    have hlastChunk : (pushRepeat out b chunk).get! ((pushRepeat out b chunk).size - 1) = b := by
      have hpushLast :=
        pushRepeat_last_get! out b b chunk hout hlast
      have hchunkNe0 : chunk ≠ 0 := by omega
      simpa [hchunkNe0] using hpushLast
    have hbit1 : bw1.bitPos < 8 := by
      exact bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit
    have hcur1 : bw1.curClearAbove := by
      exact curClearAbove_writeBits bw bitsTot codeLen.2 hbit hcur
    have hbit2 : bw2.bitPos < 8 := by
      exact bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1
    have hcur2 : bw2.curClearAbove := by
      exact curClearAbove_writeBits bw1 lenBitsTot extraLen hbit1 hcur1
    have hbitChunk : bwChunk.bitPos < 8 := by
      exact bitPos_lt_8_writeBits bw2 distBitsTot 5 hbit2
    have hcurChunk : bwChunk.curClearAbove := by
      exact curClearAbove_writeBits bw2 distBitsTot 5 hbit2 hcur2
    have hih :=
      ih rem' hlt (fuel := fuel) (bw := bwChunk) (tailBits := tailBits) (tailLen := tailLen)
        (out := pushRepeat out b chunk) (b := b) houtChunk hlastChunk htail2 hbitChunk hcurChunk
    -- reconcile `remLit` and the tail bitstream seen by the IH
    have hremEqBits :
        literalRepeatBitsTail b remLit tailBits tailLen =
          literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen := by
      simpa [hremEq]
    have hih' := hih
    rcases hih' with ⟨brAfter, hih''⟩
    refine ⟨brAfter, ?_⟩
    have hihNorm :
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit) brAfterChunk
          (pushRepeat out b chunk) =
        decodeFixedBlockFuelFast fuel brAfter (pushRepeat (pushRepeat out b chunk) b rem') := by
      -- rewrite the IH's start reader to the concrete `brAfterChunk` built by the one-step theorem
      have hihReader :
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + dist1ChunkLoopRem rem')
            (BitWriter.readerAt bwChunk
              (BitWriter.writeBits bwChunk
                (let remLit' := dist1ChunkLoopRem rem'
                 let litTail' := literalRepeatBitsTail b remLit' tailBits tailLen
                 (dist1ChunkLoopBitsTail rem' litTail'.1 litTail'.2).1)
                (let remLit' := dist1ChunkLoopRem rem'
                 let litTail' := literalRepeatBitsTail b remLit' tailBits tailLen
                 (dist1ChunkLoopBitsTail rem' litTail'.1 litTail'.2).2)).flush
              (flush_size_writeBits_le bwChunk
                (let remLit' := dist1ChunkLoopRem rem'
                 let litTail' := literalRepeatBitsTail b remLit' tailBits tailLen
                 (dist1ChunkLoopBitsTail rem' litTail'.1 litTail'.2).1)
                (let remLit' := dist1ChunkLoopRem rem'
                 let litTail' := literalRepeatBitsTail b remLit' tailBits tailLen
                 (dist1ChunkLoopBitsTail rem' litTail'.1 litTail'.2).2)) hbitChunk)
            (pushRepeat out b chunk) =
          decodeFixedBlockFuelFast fuel brAfter (pushRepeat (pushRepeat out b chunk) b rem') := hih''
      have hreaderChunk :
          brAfterChunk =
            BitWriter.readerAt bwChunk
              (BitWriter.writeBits bwChunk
                (let remLit' := dist1ChunkLoopRem rem'
                 let litTail' := literalRepeatBitsTail b remLit' tailBits tailLen
                 (dist1ChunkLoopBitsTail rem' litTail'.1 litTail'.2).1)
                (let remLit' := dist1ChunkLoopRem rem'
                 let litTail' := literalRepeatBitsTail b remLit' tailBits tailLen
                 (dist1ChunkLoopBitsTail rem' litTail'.1 litTail'.2).2)).flush
              (flush_size_writeBits_le bwChunk
                (let remLit' := dist1ChunkLoopRem rem'
                 let litTail' := literalRepeatBitsTail b remLit' tailBits tailLen
                 (dist1ChunkLoopBitsTail rem' litTail'.1 litTail'.2).1)
                (let remLit' := dist1ChunkLoopRem rem'
                 let litTail' := literalRepeatBitsTail b remLit' tailBits tailLen
                 (dist1ChunkLoopBitsTail rem' litTail'.1 litTail'.2).2)) hbitChunk := by
        have hreader0 :
            brAfterChunk =
              BitWriter.readerAt bwChunk (BitWriter.writeBits bwChunk restBits.1 restBits.2).flush
                (flush_size_writeBits_le bwChunk restBits.1 restBits.2) hbitChunk := by
          change
            BitWriter.readerAt bwChunk bwDistAll.flush
                (by
                  have hk : 5 ≤ distLenTot := by omega
                  simpa [bwChunk, distLenTot] using
                    (flush_size_writeBits_prefix bw2 distBitsTot 5 distLenTot hk))
                hbitChunk
              =
            BitWriter.readerAt bwChunk (BitWriter.writeBits bwChunk restBits.1 restBits.2).flush
                (flush_size_writeBits_le bwChunk restBits.1 restBits.2) hbitChunk
          exact readerAt_writeBits_dist1Prefix_concat (bw2 := bw2) (tailBits := restBits.1)
            (tailLen := restBits.2) (hbit2 := hbit2)
        simpa [restBits, litTail, hremEq] using hreader0
      have hfuelEq : fuel + dist1ChunkLoopSteps rem' + remLit = fuel + dist1ChunkLoopSteps rem' + dist1ChunkLoopRem rem' := by
        simpa [hremEq]
      simpa [hreaderChunk, hfuelEq] using hihReader
    have hstepsFinal : fuel + dist1ChunkLoopSteps rem' + remLit = fuel + dist1ChunkLoopSteps rem' + dist1ChunkLoopRem rem' := by
      simpa [hremEq]
    have houtFinal :
        pushRepeat (pushRepeat out b chunk) b rem' = pushRepeat out b remaining := by
      have happ := pushRepeat_append out b chunk rem'
      have hchunkLe : chunk ≤ remaining := by
        have hbounds := chooseFixedMatchChunkLen_bounds remaining hrem
        exact hbounds.2.2
      have harrith : chunk + rem' = remaining := by
        dsimp [rem']
        simpa [Nat.add_comm] using (Nat.sub_add_cancel hchunkLe)
      simpa [harrith] using happ
    exact (hstep'.trans (by simpa [hstepsFinal] using hihNorm)).trans (by simpa [houtFinal])
  · let remLit := dist1ChunkLoopRem remaining
    let litTail := literalRepeatBitsTail b remLit tailBits tailLen
    let bitsLen := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
    have hremLit : remLit = remaining := by
      dsimp [remLit]
      simpa using (dist1ChunkLoopRem_of_lt3 remaining hrem)
    have hsteps0 : dist1ChunkLoopSteps remaining = 0 := dist1ChunkLoopSteps_of_lt3 remaining hrem
    have hbits0 : bitsLen = litTail := by
      dsimp [bitsLen]
      simpa [litTail] using (dist1ChunkLoopBitsTail_of_lt3 remaining litTail.1 litTail.2 hrem)
    have hlit :=
      decodeFixedBlockFuelFast_literalRepeatBitsTail_readerAt_writeBits_exists
        (fuel := fuel) (bw := bw) (b := b) (n := remaining) (tailBits := tailBits) (tailLen := tailLen)
        (out := out) (htail2 := htail2) (hbit := hbit) (hcur := hcur)
    rcases hlit with ⟨brAfter, hlit'⟩
    refine ⟨brAfter, ?_⟩
    have hbits0' :
        dist1ChunkLoopBitsTail remaining
          (literalRepeatBitsTail b remaining tailBits tailLen).1
          (literalRepeatBitsTail b remaining tailBits tailLen).2 =
        literalRepeatBitsTail b remaining tailBits tailLen := by
      simpa using
        (dist1ChunkLoopBitsTail_of_lt3 remaining
          (literalRepeatBitsTail b remaining tailBits tailLen).1
          (literalRepeatBitsTail b remaining tailBits tailLen).2 hrem)
    simpa [remLit, litTail, bitsLen, hremLit, hsteps0, hbits0', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using hlit'

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_literalThenDist1ChunkLoopTailLits_readerAt_writeBits_exists
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (remaining tailBits tailLen : Nat) (out : ByteArray)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let remLit := dist1ChunkLoopRem remaining
    let litTail := literalRepeatBitsTail b remLit tailBits tailLen
    let chunkBits := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
    let codeLen := fixedLitLenCode b.toNat
    let bits := reverseBits codeLen.1 codeLen.2
    let bitsTot := bits ||| (chunkBits.1 <<< codeLen.2)
    let lenTot := codeLen.2 + chunkBits.2
    ∃ brAfter,
      decodeFixedBlockFuelFast (fuel + 1 + dist1ChunkLoopSteps remaining + remLit)
        (BitWriter.readerAt bw
          (BitWriter.writeBits bw bitsTot lenTot).flush
          (flush_size_writeBits_le bw bitsTot lenTot) hbit) out =
        decodeFixedBlockFuelFast fuel brAfter (pushRepeat (out.push b) b remaining) := by
  let remLit := dist1ChunkLoopRem remaining
  let litTail := literalRepeatBitsTail b remLit tailBits tailLen
  let chunkBits := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (chunkBits.1 <<< codeLen.2)
  let lenTot := codeLen.2 + chunkBits.2
  let bwAll := BitWriter.writeBits bw bitsTot lenTot
  let br0 := BitWriter.readerAt bw bwAll.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
  let br1 := BitWriter.readerAt bw1 bwAll.flush
    (by
      have hk : codeLen.2 ≤ lenTot := by omega
      simpa [bwAll, lenTot] using (flush_size_writeBits_prefix bw bitsTot codeLen.2 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit)
  have htail2Lit : 2 ≤ litTail.2 := by
    dsimp [litTail]
    exact literalRepeatBitsTail_len_ge_two b remLit tailBits tailLen htail2
  have htail2Chunk : 2 ≤ chunkBits.2 := by
    exact le_trans htail2Lit (dist1ChunkLoopBitsTail_len_ge remaining litTail.1 litTail.2)
  have hstep :=
    decodeFixedBlockFuelFast_step_literal_readerAt_writeBits
      (fuel := fuel + dist1ChunkLoopSteps remaining + remLit) (bw := bw) (b := b)
      (tailBits := chunkBits.1) (tailLen := chunkBits.2) (out := out)
      (htail2 := htail2Chunk) (hbit := hbit) (hcur := hcur)
  have hstep' :
      decodeFixedBlockFuelFast (fuel + 1 + dist1ChunkLoopSteps remaining + remLit) br0 out =
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit) br1 (out.push b) := by
    simpa [br0, br1, bwAll, remLit, litTail, chunkBits, codeLen, bits, bitsTot, lenTot,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
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
  have hchunk :=
    decodeFixedBlockFuelFast_dist1ChunkLoopTailLits_readerAt_writeBits_exists
      (fuel := fuel) (bw := bw1) (remaining := remaining) (tailBits := tailBits) (tailLen := tailLen)
      (out := out.push b) (b := b) (hout := by simp [ByteArray.size_push])
      (hlast := get!_last_push out b) (htail2 := htail2) (hbit := hbit1) (hcur := hcur1)
  rcases hchunk with ⟨brAfter, hchunk'⟩
  have hbwAll' :
      bwAll = BitWriter.writeBits bw1 chunkBits.1 chunkBits.2 := by
    dsimp [bwAll, bw1]
    simpa [hwriteBits] using hconcat
  have hreader1 :
      br1 =
        BitWriter.readerAt bw1 (BitWriter.writeBits bw1 chunkBits.1 chunkBits.2).flush
          (flush_size_writeBits_le bw1 chunkBits.1 chunkBits.2) hbit1 := by
    apply BitReader.ext
    · dsimp [br1]
      simpa [hbwAll'] using congrArg BitWriter.flush hbwAll'
    · simp [br1, BitWriter.readerAt]
    · simp [br1, BitWriter.readerAt]
  have hchunkNorm :
      decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit) br1 (out.push b) =
        decodeFixedBlockFuelFast fuel brAfter (pushRepeat (out.push b) b remaining) := by
    simpa [hreader1]
      using hchunk'
  refine ⟨brAfter, ?_⟩
  exact hstep'.trans hchunkNorm

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_dist1ChunkLoopTailLits_readerAt_writeBits_tail
    (fuel : Nat) (bw : BitWriter) (remaining tailBits tailLen : Nat)
    (out : ByteArray) (b : UInt8)
    (hout : 0 < out.size) (hlast : out.get! (out.size - 1) = b)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let remLit := dist1ChunkLoopRem remaining
    let litTail := literalRepeatBitsTail b remLit tailBits tailLen
    let bitsLen := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
    decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit)
      (BitWriter.readerAt bw
        (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
        (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out =
      decodeFixedBlockFuelFast fuel
        (dist1ChunkLoopTailLitsTailStartReader bw remaining b tailBits tailLen hbit)
        (pushRepeat out b remaining) := by
  revert fuel bw tailBits tailLen out b hout hlast htail2 hbit hcur
  refine Nat.strong_induction_on remaining ?_
  intro remaining ih fuel bw tailBits tailLen out b hout hlast htail2 hbit hcur
  by_cases hrem : 3 ≤ remaining
  · let chunk := chooseFixedMatchChunkLen remaining
    let rem' := remaining - chunk
    let remLit := dist1ChunkLoopRem rem'
    let remLit0 := dist1ChunkLoopRem remaining
    have hremEq : remLit0 = remLit := by
      dsimp [remLit0, rem']
      simpa [chunk] using (dist1ChunkLoopRem_of_ge3 remaining hrem)
    let litTail := literalRepeatBitsTail b remLit tailBits tailLen
    let bitsLen := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
    let restBits := dist1ChunkLoopBitsTail rem' litTail.1 litTail.2
    let chunkInfo := fixedLenMatchInfo chunk
    let sym := chunkInfo.1
    let extraBits := chunkInfo.2.1
    let extraLen := chunkInfo.2.2
    let codeLen := fixedLitLenCode sym
    let symBits := reverseBits codeLen.1 codeLen.2
    let distBitsTot := (0 : Nat) ||| (restBits.1 <<< 5)
    let distLenTot := 5 + restBits.2
    let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
    let lenLenTot := extraLen + distLenTot
    let bitsTot := symBits ||| (lenBitsTot <<< codeLen.2)
    let lenTot := codeLen.2 + lenLenTot
    let bw1 := BitWriter.writeBits bw bitsTot codeLen.2
    let bw2 := BitWriter.writeBits bw1 lenBitsTot extraLen
    let bwChunk := BitWriter.writeBits bw2 distBitsTot 5
    let bwDistAll := BitWriter.writeBits bw2 distBitsTot distLenTot
    let brAfterChunk := BitWriter.readerAt bwChunk bwDistAll.flush
      (by
        have hk : 5 ≤ distLenTot := by omega
        simpa [bwChunk, distLenTot] using
          (flush_size_writeBits_prefix bw2 distBitsTot 5 distLenTot hk))
      (bitPos_lt_8_writeBits bw2 distBitsTot 5
        (bitPos_lt_8_writeBits bw1 lenBitsTot extraLen
          (bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit)))
    have hstepsGe : dist1ChunkLoopSteps remaining = 1 + dist1ChunkLoopSteps rem' := by
      simpa [chunk, rem'] using (dist1ChunkLoopSteps_of_ge3 remaining hrem)
    have hbitsGe := dist1ChunkLoopBitsTail_of_ge3 remaining litTail.1 litTail.2 hrem
    have hbitsPair : bitsLen = (bitsTot, lenTot) := by
      dsimp [bitsLen]
      simpa [chunk, rem', restBits, chunkInfo, sym, extraBits, extraLen, codeLen, symBits,
        distBitsTot, distLenTot, lenBitsTot, lenLenTot, bitsTot, lenTot] using hbitsGe
    have hbitsEq : bitsLen.1 = bitsTot := congrArg Prod.fst hbitsPair
    have hlenEq : bitsLen.2 = lenTot := congrArg Prod.snd hbitsPair
    have hchunkSub : rem' < remaining := by
      simpa [chunk, rem'] using (chooseFixedMatchChunkLen_sub_lt remaining hrem)
    have hchunkPos : 0 < chunk := by
      have hbounds := chooseFixedMatchChunkLen_bounds remaining hrem
      omega
    have hstep :=
      decodeFixedBlockFuelFast_step_chooseFixedMatchChunkLen_dist1_readerAt_writeBits
        (fuel := fuel + dist1ChunkLoopSteps rem' + remLit0) (bw := bw)
        (remaining := remaining) (tailBits := restBits.1) (tailLen := restBits.2) (out := out)
        (hrem := hrem) (hout := hout) (hbit := hbit) (hcur := hcur)
    have hstep' :
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit0)
          (BitWriter.readerAt bw
            (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
            (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out =
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit0)
          brAfterChunk (pushRepeat out b chunk) := by
      have hstepLocal :
          decodeFixedBlockFuelFast (fuel + (dist1ChunkLoopSteps rem' + remLit0) + 1)
            (BitWriter.readerAt bw
              (BitWriter.writeBits bw bitsTot lenTot).flush
              (flush_size_writeBits_le bw bitsTot lenTot) hbit) out =
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit0)
            brAfterChunk (pushRepeat out (out.get! (out.size - 1)) chunk) := by
        simpa [chunk, rem', restBits, chunkInfo, sym, extraBits, extraLen, codeLen, symBits,
          distBitsTot, distLenTot, lenBitsTot, lenLenTot, bitsTot, lenTot, bw1, bw2, bwChunk,
          bwDistAll, brAfterChunk, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
      have hreader :
          BitWriter.readerAt bw
            (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
            (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit
            =
          BitWriter.readerAt bw
            (BitWriter.writeBits bw bitsTot lenTot).flush
            (flush_size_writeBits_le bw bitsTot lenTot) hbit := by
        simp [hbitsEq, hlenEq]
      have hpushLast :
          pushRepeat out (out.get! (out.size - 1)) chunk = pushRepeat out b chunk := by
        exact congrArg (fun x => pushRepeat out x chunk) hlast
      calc
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit0)
            (BitWriter.readerAt bw
              (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
              (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out
            =
          decodeFixedBlockFuelFast (fuel + (1 + dist1ChunkLoopSteps rem') + remLit0)
            (BitWriter.readerAt bw
              (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
              (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out := by
              simp [hstepsGe, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ =
          decodeFixedBlockFuelFast (fuel + (dist1ChunkLoopSteps rem' + remLit0) + 1)
            (BitWriter.readerAt bw
              (BitWriter.writeBits bw bitsTot lenTot).flush
              (flush_size_writeBits_le bw bitsTot lenTot) hbit) out := by
              simp [hreader, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ =
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit0)
            brAfterChunk (pushRepeat out (out.get! (out.size - 1)) chunk) := hstepLocal
        _ =
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit0)
            brAfterChunk (pushRepeat out b chunk) := by
              simp [hpushLast]
    have hbit1 : bw1.bitPos < 8 := by
      exact bitPos_lt_8_writeBits bw bitsTot codeLen.2 hbit
    have hcur1 : bw1.curClearAbove := by
      exact curClearAbove_writeBits bw bitsTot codeLen.2 hbit hcur
    have hbit2 : bw2.bitPos < 8 := by
      exact bitPos_lt_8_writeBits bw1 lenBitsTot extraLen hbit1
    have hcur2 : bw2.curClearAbove := by
      exact curClearAbove_writeBits bw1 lenBitsTot extraLen hbit1 hcur1
    have hbitChunk : bwChunk.bitPos < 8 := by
      exact bitPos_lt_8_writeBits bw2 distBitsTot 5 hbit2
    have hcurChunk : bwChunk.curClearAbove := by
      exact curClearAbove_writeBits bw2 distBitsTot 5 hbit2 hcur2
    have houtChunk : 0 < (pushRepeat out b chunk).size := by
      exact pushRepeat_pos out b chunk hout
    have hlastChunk : (pushRepeat out b chunk).get! ((pushRepeat out b chunk).size - 1) = b := by
      have hpushLast := pushRepeat_last_get! out b b chunk hout hlast
      have hchunkNe0 : chunk ≠ 0 := by omega
      simpa [hchunkNe0] using hpushLast
    have hih :=
      ih rem' hchunkSub (fuel := fuel) (bw := bwChunk)
        (tailBits := tailBits) (tailLen := tailLen)
        (out := pushRepeat out b chunk) (b := b)
        houtChunk hlastChunk htail2 hbitChunk hcurChunk
    have hreaderChunk :
        brAfterChunk =
          BitWriter.readerAt bwChunk
            (BitWriter.writeBits bwChunk restBits.1 restBits.2).flush
            (flush_size_writeBits_le bwChunk restBits.1 restBits.2) hbitChunk := by
      change
        BitWriter.readerAt bwChunk bwDistAll.flush
            (by
              have hk : 5 ≤ distLenTot := by omega
              simpa [bwChunk, distLenTot] using
                (flush_size_writeBits_prefix bw2 distBitsTot 5 distLenTot hk))
            hbitChunk
          =
        BitWriter.readerAt bwChunk
          (BitWriter.writeBits bwChunk restBits.1 restBits.2).flush
          (flush_size_writeBits_le bwChunk restBits.1 restBits.2) hbitChunk
      exact readerAt_writeBits_dist1Prefix_concat
        (bw2 := bw2) (tailBits := restBits.1) (tailLen := restBits.2) (hbit2 := hbit2)
    have hih' :
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit0)
          brAfterChunk (pushRepeat out b chunk) =
        decodeFixedBlockFuelFast fuel
          (dist1ChunkLoopTailLitsTailStartReader bwChunk rem' b tailBits tailLen hbitChunk)
          (pushRepeat (pushRepeat out b chunk) b rem') := by
      have hfuelEq :
          fuel + dist1ChunkLoopSteps rem' + remLit0 =
            fuel + dist1ChunkLoopSteps rem' + remLit := by
        simp [hremEq]
      have hreaderIH :
          BitWriter.readerAt bwChunk
            (BitWriter.writeBits bwChunk restBits.1 restBits.2).flush
            (flush_size_writeBits_le bwChunk restBits.1 restBits.2) hbitChunk
            =
          BitWriter.readerAt bwChunk
            (BitWriter.writeBits bwChunk
              (dist1ChunkLoopBitsTail rem'
                (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).1
                (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).2).1
              (dist1ChunkLoopBitsTail rem'
                (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).1
                (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).2).2).flush
            (flush_size_writeBits_le bwChunk
              (dist1ChunkLoopBitsTail rem'
                (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).1
                (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).2).1
              (dist1ChunkLoopBitsTail rem'
                (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).1
                (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).2).2)
            hbitChunk := by
        rfl
      calc
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit0)
            brAfterChunk (pushRepeat out b chunk)
            =
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit0)
            (BitWriter.readerAt bwChunk
              (BitWriter.writeBits bwChunk restBits.1 restBits.2).flush
              (flush_size_writeBits_le bwChunk restBits.1 restBits.2) hbitChunk)
            (pushRepeat out b chunk) := by
              simp [hreaderChunk]
        _ =
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit)
            (BitWriter.readerAt bwChunk
              (BitWriter.writeBits bwChunk restBits.1 restBits.2).flush
              (flush_size_writeBits_le bwChunk restBits.1 restBits.2) hbitChunk)
            (pushRepeat out b chunk) := by
              simp [hfuelEq]
        _ =
          decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit)
            (BitWriter.readerAt bwChunk
              (BitWriter.writeBits bwChunk
                (dist1ChunkLoopBitsTail rem'
                  (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).1
                  (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).2).1
                (dist1ChunkLoopBitsTail rem'
                  (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).1
                  (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).2).2).flush
              (flush_size_writeBits_le bwChunk
                (dist1ChunkLoopBitsTail rem'
                  (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).1
                  (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).2).1
                (dist1ChunkLoopBitsTail rem'
                  (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).1
                  (literalRepeatBitsTail b (dist1ChunkLoopRem rem') tailBits tailLen).2).2)
              hbitChunk)
            (pushRepeat out b chunk) := by
              simp [hreaderIH]
        _ =
          decodeFixedBlockFuelFast fuel
            (dist1ChunkLoopTailLitsTailStartReader bwChunk rem' b tailBits tailLen hbitChunk)
            (pushRepeat (pushRepeat out b chunk) b rem') := hih
    have hreaderGe :
        dist1ChunkLoopTailLitsTailStartReader bw remaining b tailBits tailLen hbit =
          dist1ChunkLoopTailLitsTailStartReaderStep bw remaining b tailBits tailLen hbit := by
      exact dist1ChunkLoopTailLitsTailStartReader_of_ge3
        (bw := bw) (remaining := remaining) (b := b)
        (tailBits := tailBits) (tailLen := tailLen) (hbit := hbit) (hrem := hrem)
    have hreaderStep :
        dist1ChunkLoopTailLitsTailStartReaderStep bw remaining b tailBits tailLen hbit =
          dist1ChunkLoopTailLitsTailStartReader bwChunk rem' b tailBits tailLen hbitChunk := by
      dsimp [dist1ChunkLoopTailLitsTailStartReaderStep, chunk, rem', remLit, litTail, restBits,
        chunkInfo, sym, extraBits, extraLen, codeLen, symBits, distBitsTot, lenBitsTot,
        bitsTot, bw1, bw2, bwChunk]
    have houtFinal :
        pushRepeat (pushRepeat out b chunk) b rem' = pushRepeat out b remaining := by
      have happ := pushRepeat_append out b chunk rem'
      have hchunkLe : chunk ≤ remaining := by
        have hbounds := chooseFixedMatchChunkLen_bounds remaining hrem
        exact hbounds.2.2
      have harrith : chunk + rem' = remaining := by
        dsimp [rem']
        simpa [Nat.add_comm] using (Nat.sub_add_cancel hchunkLe)
      simpa [harrith] using happ
    have hstartEq :
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit0)
          (BitWriter.readerAt bw
            (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
            (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out =
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit0)
          (BitWriter.readerAt bw
            (BitWriter.writeBits bw
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b remLit0 tailBits tailLen).1
                (literalRepeatBitsTail b remLit0 tailBits tailLen).2).1
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b remLit0 tailBits tailLen).1
                (literalRepeatBitsTail b remLit0 tailBits tailLen).2).2).flush
            (flush_size_writeBits_le bw
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b remLit0 tailBits tailLen).1
                (literalRepeatBitsTail b remLit0 tailBits tailLen).2).1
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b remLit0 tailBits tailLen).1
                (literalRepeatBitsTail b remLit0 tailBits tailLen).2).2) hbit) out := by
      have hbits0 :
          bitsLen =
            dist1ChunkLoopBitsTail remaining
              (literalRepeatBitsTail b remLit0 tailBits tailLen).1
              (literalRepeatBitsTail b remLit0 tailBits tailLen).2 := by
        dsimp [bitsLen, litTail]
        simp [hremEq]
      simpa [hbits0]
    calc
      decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + dist1ChunkLoopRem remaining)
          (BitWriter.readerAt bw
            (BitWriter.writeBits bw
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b (dist1ChunkLoopRem remaining) tailBits tailLen).1
                (literalRepeatBitsTail b (dist1ChunkLoopRem remaining) tailBits tailLen).2).1
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b (dist1ChunkLoopRem remaining) tailBits tailLen).1
                (literalRepeatBitsTail b (dist1ChunkLoopRem remaining) tailBits tailLen).2).2).flush
            (flush_size_writeBits_le bw
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b (dist1ChunkLoopRem remaining) tailBits tailLen).1
                (literalRepeatBitsTail b (dist1ChunkLoopRem remaining) tailBits tailLen).2).1
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b (dist1ChunkLoopRem remaining) tailBits tailLen).1
                (literalRepeatBitsTail b (dist1ChunkLoopRem remaining) tailBits tailLen).2).2) hbit) out
          =
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit0)
          (BitWriter.readerAt bw
            (BitWriter.writeBits bw
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b remLit0 tailBits tailLen).1
                (literalRepeatBitsTail b remLit0 tailBits tailLen).2).1
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b remLit0 tailBits tailLen).1
                (literalRepeatBitsTail b remLit0 tailBits tailLen).2).2).flush
            (flush_size_writeBits_le bw
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b remLit0 tailBits tailLen).1
                (literalRepeatBitsTail b remLit0 tailBits tailLen).2).1
              (dist1ChunkLoopBitsTail remaining
                (literalRepeatBitsTail b remLit0 tailBits tailLen).1
                (literalRepeatBitsTail b remLit0 tailBits tailLen).2).2) hbit) out := by
            simp [remLit0]
      _ =
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps remaining + remLit0)
          (BitWriter.readerAt bw
            (BitWriter.writeBits bw bitsLen.1 bitsLen.2).flush
            (flush_size_writeBits_le bw bitsLen.1 bitsLen.2) hbit) out := by
            simpa using hstartEq.symm
      _ =
        decodeFixedBlockFuelFast (fuel + dist1ChunkLoopSteps rem' + remLit0)
          brAfterChunk (pushRepeat out b chunk) := hstep'
      _ =
        decodeFixedBlockFuelFast fuel
          (dist1ChunkLoopTailLitsTailStartReader bwChunk rem' b tailBits tailLen hbitChunk)
          (pushRepeat (pushRepeat out b chunk) b rem') := hih'
      _ =
        decodeFixedBlockFuelFast fuel
          (dist1ChunkLoopTailLitsTailStartReaderStep bw remaining b tailBits tailLen hbit)
          (pushRepeat (pushRepeat out b chunk) b rem') := by
            simp [hreaderStep]
      _ =
        decodeFixedBlockFuelFast fuel
          (dist1ChunkLoopTailLitsTailStartReader bw remaining b tailBits tailLen hbit)
          (pushRepeat (pushRepeat out b chunk) b rem') := by
            simp [hreaderGe]
      _ =
        decodeFixedBlockFuelFast fuel
          (dist1ChunkLoopTailLitsTailStartReader bw remaining b tailBits tailLen hbit)
          (pushRepeat out b remaining) := by
            simp [houtFinal]
  · have hmain :=
      decodeFixedBlockFuelFast_dist1ChunkLoopTailLits_readerAt_writeBits_tail_of_lt3
        (fuel := fuel) (bw := bw) (remaining := remaining) (tailBits := tailBits)
        (tailLen := tailLen) (out := out) (b := b)
        (htail2 := htail2) (hbit := hbit) (hcur := hcur) (hrem := hrem)
    simpa using hmain

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma decodeFixedBlockFuelFast_dist1Run_readerAt_writeBits_exists
    (fuel : Nat) (bw : BitWriter) (b : UInt8) (remaining tailBits tailLen : Nat) (out : ByteArray)
    (htail2 : 2 ≤ tailLen) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    ∃ brAfter,
      decodeFixedBlockFuelFast (fuel + dist1RunSteps remaining)
        (BitWriter.readerAt bw
          (BitWriter.writeBits bw (dist1RunBitsTail b remaining tailBits tailLen).1
            (dist1RunBitsTail b remaining tailBits tailLen).2).flush
          (flush_size_writeBits_le bw
            (dist1RunBitsTail b remaining tailBits tailLen).1
            (dist1RunBitsTail b remaining tailBits tailLen).2) hbit) out =
        decodeFixedBlockFuelFast fuel brAfter (dist1RunOut out b remaining) := by
  rcases
    (decodeFixedBlockFuelFast_literalThenDist1ChunkLoopTailLits_readerAt_writeBits_exists
      (fuel := fuel) (bw := bw) (b := b) (remaining := remaining)
      (tailBits := tailBits) (tailLen := tailLen) (out := out)
      (htail2 := htail2) (hbit := hbit) (hcur := hcur))
    with ⟨brAfter, h⟩
  refine ⟨brAfter, ?_⟩
  simpa [dist1RunBitsTail, dist1RunSteps, dist1RunOut, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h


end Png
end Bitmaps
