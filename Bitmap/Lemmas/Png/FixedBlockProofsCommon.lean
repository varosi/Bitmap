import Bitmap.Lemmas.Png.FixedBlockBase

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

lemma fixedLitLenRevCodeFast_eq (sym : Nat) (h : sym < 288) :
    fixedLitLenRevCodeFast sym =
      let codeLen := fixedLitLenCode sym
      (reverseBits codeLen.1 codeLen.2, codeLen.2) := by
  unfold fixedLitLenRevCodeFast
  have htab : sym < fixedLitLenRevTable.size := by simpa using h
  simp [htab, fixedLitLenRevTable]

@[simp] lemma writeBits_zero (bw : BitWriter) (bits : Nat) :
    BitWriter.writeBits bw bits 0 = bw := by
  rfl

@[simp] lemma writeFixedLiteralFast_eq_writeBits (bw : BitWriter) (b : UInt8) :
    BitWriter.writeFixedLiteralFast bw b =
      let codeLen := fixedLitLenCode b.toNat
      BitWriter.writeBits bw (reverseBits codeLen.1 codeLen.2) codeLen.2 := by
  unfold BitWriter.writeFixedLiteralFast
  have hsym : b.toNat < 288 := by
    exact lt_trans (UInt8.toNat_lt b) (by decide)
  simp [fixedLitLenRevCodeFast_eq, hsym]

lemma readBitsFastU32_readerAt_writeBits_prefix (bw : BitWriter) (bits len k : Nat)
    (hk : k ≤ len) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bw' := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
    br.readBitsFastU32 k
      (by
        simpa [br, bw'] using (readerAt_writeBits_bound (bw := bw) (bits := bits) (len := len)
          (k := k) hk hbit)) =
      (bits % 2 ^ k,
        BitWriter.readerAt (BitWriter.writeBits bw bits k) bw'.flush
          (by
            simpa [bw'] using (flush_size_writeBits_prefix bw bits k len hk))
          (bitPos_lt_8_writeBits bw bits k hbit)) := by
  let bw' := BitWriter.writeBits bw bits len
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
  let brk := BitWriter.readerAt (BitWriter.writeBits bw bits k) bw'.flush
    (by simpa [bw'] using (flush_size_writeBits_prefix bw bits k len hk))
    (bitPos_lt_8_writeBits bw bits k hbit)
  have hread : br.bitIndex + k ≤ br.data.size * 8 := by
    simpa [br, bw'] using (readerAt_writeBits_bound (bw := bw) (bits := bits) (len := len)
      (k := k) hk hbit)
  have hbits :
      br.readBits k hread = (bits % 2 ^ k, brk) := by
    simpa [br, bw', brk] using
      (readBits_readerAt_writeBits_prefix (bw := bw) (bits := bits) (len := len) (k := k)
        (hk := hk) (hbit := hbit) (hcur := hcur))
  have hfastEq : br.readBitsFastU32 k hread = br.readBits k hread := by
    calc
      br.readBitsFastU32 k hread = br.readBitsAux k := by
        exact readBitsFastU32_eq_readBitsAux (br := br) (n := k) (h := hread)
      _ = br.readBits k hread := by
        symm
        exact readBits_eq_readBitsAux (br := br) (n := k) (h := hread)
  calc
    br.readBitsFastU32 k hread = br.readBits k hread := hfastEq
    _ = (bits % 2 ^ k, brk) := hbits

-- Distance symbol 0 in DEFLATE fixed coding decodes to distance 1.
lemma decodeDistance_zero (br : BitReader)
    (hbits : br.bitIndex +
      distExtra[0]'(by
        simpa [distExtra] using (Nat.succ_pos 29)) ≤ br.data.size * 8) :
    decodeDistance 0 br
      (by
        simpa [distBases] using (Nat.succ_pos 29))
      hbits = (1, br) := by
  simp [decodeDistance, distBases, distExtra]

-- `copyDistance` dispatches to the optimized distance-1 path and does not fail on nonempty output.
lemma copyDistance_one_ne_none (out : ByteArray) (len : Nat) (hout : 0 < out.size) :
    copyDistance out 1 len ≠ none := by
  unfold copyDistance copyDistanceFast
  have hbad : ¬ (1 = 0 ∨ 1 > out.size) := by
    intro h
    rcases h with h0 | hgt
    · omega
    · omega
  have hne : out ≠ ByteArray.empty := by
    intro he
    have hsize0 : out.size = 0 := by simpa [he]
    omega
  simp [hbad, hne]

def pushRepeat (out : ByteArray) (b : UInt8) : Nat → ByteArray
  | 0 => out
  | n + 1 => pushRepeat (out.push b) b n

@[simp] lemma pushRepeat_zero (out : ByteArray) (b : UInt8) :
    pushRepeat out b 0 = out := rfl

@[simp] lemma pushRepeat_succ (out : ByteArray) (b : UInt8) (n : Nat) :
    pushRepeat out b (n + 1) = pushRepeat (out.push b) b n := rfl

@[simp] lemma pushRepeat_size (out : ByteArray) (b : UInt8) (n : Nat) :
    (pushRepeat out b n).size = out.size + n := by
  induction n generalizing out with
  | zero =>
      simp [pushRepeat]
  | succ n ih =>
      simp [pushRepeat, ih, ByteArray.size_push, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma pushRepeat_pos (out : ByteArray) (b : UInt8) (n : Nat) (hout : 0 < out.size) :
    0 < (pushRepeat out b n).size := by
  simpa [pushRepeat_size] using Nat.lt_of_lt_of_le hout (Nat.le_add_right out.size n)

lemma pushRepeat_append (out : ByteArray) (b : UInt8) (n m : Nat) :
    pushRepeat (pushRepeat out b n) b m = pushRepeat out b (n + m) := by
  induction n generalizing out with
  | zero =>
      simp
  | succ n ih =>
      simp [pushRepeat, ih, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma pushRepeat_last_eq
    (out : ByteArray) (b last : UInt8) (n : Nat)
    (hout : 0 < out.size)
    (hlast : out[out.size - 1]'(by omega) = last) :
    (pushRepeat out b n)[(pushRepeat out b n).size - 1]'(by
        have hpos : 0 < (pushRepeat out b n).size := pushRepeat_pos out b n hout
        omega) =
      (if n = 0 then last else b) := by
  induction n generalizing out last with
  | zero =>
      simp [pushRepeat, hlast]
  | succ n ih =>
      have hout' : 0 < (out.push b).size := by
        simp [ByteArray.size_push]
      have hlast' : (out.push b)[(out.push b).size - 1]'(by
          simp [ByteArray.size_push]) = b := by
        have hget : (out.push b)[out.size]'(by simp [ByteArray.size_push]) = b := by
          simpa using (ByteArray.get_push_eq out b)
        simpa [ByteArray.size_push] using hget
      have hrec := ih (out := out.push b) (last := b) hout' hlast'
      have hsizeSucc : (pushRepeat out b (n + 1)).size = (pushRepeat (out.push b) b n).size := by
        simp [pushRepeat]
      have hidxSucc :
          (pushRepeat out b (n + 1))[((pushRepeat out b (n + 1)).size - 1)]'(by
              have hpos : 0 < (pushRepeat out b (n + 1)).size := pushRepeat_pos out b (n + 1) hout
              omega) =
          (pushRepeat (out.push b) b n)[((pushRepeat (out.push b) b n).size - 1)]'(by
              have hpos : 0 < (pushRepeat (out.push b) b n).size := pushRepeat_pos (out.push b) b n hout'
              omega) := by
        simp [pushRepeat]
      have hb : (if n = 0 then b else b) = b := by
        cases n <;> rfl
      have hlhs := hrec.trans hb
      have hne : n + 1 ≠ 0 := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_ne_zero n)
      have hrhs : (if n + 1 = 0 then last else b) = b := if_neg hne
      rw [hidxSucc]
      exact hlhs.trans hrhs.symm

lemma pushRepeat_last_get!
    (out : ByteArray) (b last : UInt8) (n : Nat)
    (hout : 0 < out.size)
    (hlast : out.get! (out.size - 1) = last) :
    (pushRepeat out b n).get! ((pushRepeat out b n).size - 1) =
      (if n = 0 then last else b) := by
  have hlastLt : out.size - 1 < out.size := by
    omega
  have hlastIdx : out[out.size - 1]'hlastLt = last := by
    simpa [ByteArray.get!, getElem!_pos, hlastLt] using hlast
  have hidx :=
    pushRepeat_last_eq out b last n hout hlastIdx
  have hpushPos : 0 < (pushRepeat out b n).size := pushRepeat_pos out b n hout
  have hpushLt : (pushRepeat out b n).size - 1 < (pushRepeat out b n).size := by
    omega
  have hpushLtData : (pushRepeat out b n).size - 1 < (pushRepeat out b n).data.size := by
    simpa using hpushLt
  have hidxData :
      (pushRepeat out b n).data[(pushRepeat out b n).size - 1]'hpushLt = (if n = 0 then last else b) := by
    simpa [ByteArray.get] using hidx
  have hbang :
      (pushRepeat out b n).data[(pushRepeat out b n).size - 1]! =
        (pushRepeat out b n).data[(pushRepeat out b n).size - 1]'hpushLtData := by
    exact getElem!_pos ((pushRepeat out b n).data) ((pushRepeat out b n).size - 1) hpushLtData
  calc
    (pushRepeat out b n).get! ((pushRepeat out b n).size - 1)
        = (pushRepeat out b n).data[(pushRepeat out b n).size - 1]! := by
            simp [ByteArray.get!]
    _ = (pushRepeat out b n).data[(pushRepeat out b n).size - 1]'hpushLtData := hbang
    _ = (if n = 0 then last else b) := by
          have hprf : hpushLtData = hpushLt := Subsingleton.elim _ _
          simpa [hprf] using hidxData

@[simp] lemma get!_last_push (out : ByteArray) (b : UInt8) :
    (out.push b).get! ((out.push b).size - 1) = b := by
  have hidx : (out.push b).size - 1 = out.size := by
    simp [ByteArray.size_push]
  calc
    (out.push b).get! ((out.push b).size - 1)
        = (out.push b).get! out.size := by simp [hidx]
    _ = b := by
          have hlt : out.size < (out.push b).data.size := by
            simpa [ByteArray.size_push] using Nat.lt_succ_self out.size
          have hbang :
              (out.push b).data[out.size]! = (out.push b).data[out.size]'hlt := by
            exact getElem!_pos (out.push b).data out.size hlt
          calc
            (out.push b).get! out.size = (out.push b).data[out.size]! := by simp [ByteArray.get!]
            _ = (out.push b).data[out.size]'hlt := hbang
            _ = b := by
                  change (out.push b)[out.size]'(by
                    simpa [ByteArray.size_push] using Nat.lt_succ_self out.size) = b
                  exact ByteArray.get_push_eq out b

lemma pushRepeat_push_eq (out : ByteArray) (b : UInt8) (n : Nat) :
    pushRepeat (out.push b) b n = pushRepeat out b (n + 1) := by
  simpa using (pushRepeat_succ out b n).symm

lemma foldl_push_range'_eq_pushRepeat (out : ByteArray) (b : UInt8) (start len : Nat) :
    List.foldl (fun acc _ => acc.push b) out (List.range' start len 1) =
      pushRepeat out b len := by
  induction len generalizing out start with
  | zero =>
      simp [pushRepeat]
  | succ n ih =>
      simp [List.range'_succ, pushRepeat, ih]

lemma idRun_pushRange_eq_pushRepeat (out : ByteArray) (b : UInt8) (len : Nat) :
    (Id.run do
      let mut out := out
      for _ in [0:len] do
        out := out.push b
      return out) = pushRepeat out b len := by
  simpa [Std.Legacy.Range.forIn_eq_forIn_range'] using
    (foldl_push_range'_eq_pushRepeat out b 0 len)

lemma copyDistance_one_eq_pushRepeat (out : ByteArray) (len : Nat) (hout : 0 < out.size) :
    copyDistance out 1 len =
      some (pushRepeat out (out.get! (out.size - 1)) len) := by
  unfold copyDistance copyDistanceFast
  have hbad : ¬ (1 = 0 ∨ 1 > out.size) := by
    intro h
    rcases h with h0 | hgt
    · omega
    · omega
  have hne : out ≠ ByteArray.empty := by
    intro he
    have hsize0 : out.size = 0 := by simpa [he]
    omega
  have hloop := idRun_pushRange_eq_pushRepeat out (out.get! (out.size - 1)) len
  simpa [hbad, hne] using congrArg some hloop

-- If the next five bits are zero, the fixed distance decoder reads symbol 0.
lemma decodeFixedDistanceSym_readerAt_writeBits_zero (bw : BitWriter) (restBits restLen : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := (0 : Nat) ||| (restBits <<< 5)
    let lenTot := 5 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeFixedDistanceSym br =
      some (0,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot 5) bw'.flush
          (by
            have hk : 5 ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot 5 hbit)) := by
  let bitsTot := (0 : Nat) ||| (restBits <<< 5)
  let lenTot := 5 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  have hread5 : br.bitIndex + 5 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 5)
        (hk := by omega) hbit)
  let br5 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 5) bw'.flush
      (by
        have hk : 5 ≤ lenTot := by omega
        simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  have hbits5 :
      br.readBits 5 hread5 = (bitsTot % 2 ^ 5, br5) := by
    simpa [br, bw', br5, lenTot] using
      (readBits_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 5)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hmod0 : bitsTot % 2 ^ 5 = 0 := by
    have h := mod_two_pow_or_shift (a := (0 : Nat)) (b := restBits) (k := 5) (len := 5) (by decide)
    simpa [bitsTot] using h
  have hbits5' : br.readBitsFast 5 hread5 = (0, br5) := by
    have hbits5'' : br.readBits 5 hread5 = (0, br5) := by simpa [hmod0] using hbits5
    simpa [readBitsFast_eq_readBits (br := br) (n := 5) (h := hread5)] using hbits5''
  have hrev0 : reverseBits 0 5 = 0 := by decide
  have hbits5_any : ∀ h' : br.bitIndex + 5 ≤ br.data.size * 8, br.readBitsFast 5 h' = (0, br5) := by
    intro h'
    have hreadEq : br.readBits 5 h' = br.readBits 5 hread5 := by
      exact readBits_proof_irrel (br := br) (n := 5) (h1 := h') (h2 := hread5)
    calc
      br.readBitsFast 5 h' = br.readBits 5 h' := by
        simp [readBitsFast_eq_readBits]
      _ = br.readBits 5 hread5 := hreadEq
      _ = (0, br5) := by
        simpa [readBitsFast_eq_readBits (br := br) (n := 5) (h := hread5)] using hbits5'
  have hres : decodeFixedDistanceSym br = some (0, br5) := by
    by_cases hcond : br.bitIndex + 5 ≤ br.data.size * 8
    · have hfast : br.readBitsFast 5 hcond = (0, br5) := hbits5_any hcond
      simp [decodeFixedDistanceSym, hcond, hfast, hrev0]
    · exact (False.elim <| hcond hread5)
  simpa [bitsTot, lenTot, bw', br, br5] using hres

lemma decodeFixedDistanceSym_zero_decodeDistance_zero_copyDistance_one_exists
    (bw : BitWriter) (restBits restLen matchLen : Nat) (out : ByteArray)
    (hout : 0 < out.size) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := (0 : Nat) ||| (restBits <<< 5)
    let lenTot := 5 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br5 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 5) bw'.flush
      (by
        have hk : 5 ≤ lenTot := by omega
        simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot 5 hbit)
    ∃ hdist hbitsD,
      decodeFixedDistanceSym br = some (0, br5) ∧
      decodeDistance 0 br5 hdist hbitsD = (1, br5) ∧
      copyDistance out 1 matchLen = some (pushRepeat out (out.get! (out.size - 1)) matchLen) := by
  let bitsTot := (0 : Nat) ||| (restBits <<< 5)
  let lenTot := 5 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br5 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 5) bw'.flush
    (by
      have hk : 5 ≤ lenTot := by omega
      simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  have hdist : 0 < distBases.size := by
    simpa [distBases] using (Nat.succ_pos 29)
  have hbit5 : (BitWriter.writeBits bw bitsTot 5).bitPos < 8 := by
    exact bitPos_lt_8_writeBits bw bitsTot 5 hbit
  have hflush5 : (BitWriter.writeBits bw bitsTot 5).flush.size ≤ bw'.flush.size := by
    have hk : 5 ≤ lenTot := by omega
    simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot 5 lenTot hk)
  have hbitIndex5_le : br5.bitIndex ≤ br5.data.size * 8 := by
    have hcount_le :
        (BitWriter.writeBits bw bitsTot 5).bitCount ≤
          (BitWriter.writeBits bw bitsTot 5).flush.size * 8 := by
      simpa using (flush_size_mul_ge_bitCount (bw := BitWriter.writeBits bw bitsTot 5) hbit5)
    have hflush_mul :
        (BitWriter.writeBits bw bitsTot 5).flush.size * 8 ≤ bw'.flush.size * 8 := by
      exact Nat.mul_le_mul_right 8 hflush5
    have hflush_mul' :
        (BitWriter.writeBits bw bitsTot 5).flush.size * 8 ≤ br5.data.size * 8 := by
      simpa [br5] using hflush_mul
    calc
      br5.bitIndex = (BitWriter.writeBits bw bitsTot 5).bitCount := by
        simp [br5]
      _ ≤ (BitWriter.writeBits bw bitsTot 5).flush.size * 8 := hcount_le
      _ ≤ br5.data.size * 8 := hflush_mul'
  have hbitsD : br5.bitIndex +
      distExtra[0]'(by
        simpa [distExtra] using (Nat.succ_pos 29)) ≤ br5.data.size * 8 := by
    simpa [distExtra] using hbitIndex5_le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hdist
  · exact hbitsD
  · simpa [br, bw', br5, bitsTot, lenTot] using
      (decodeFixedDistanceSym_readerAt_writeBits_zero (bw := bw) (restBits := restBits) (restLen := restLen)
        (hbit := hbit) (hcur := hcur))
  · simp [decodeDistance, distBases, distExtra]
  · exact copyDistance_one_eq_pushRepeat out matchLen hout

set_option maxRecDepth 100000 in
lemma decodeFixedLiteralSymFast9_readerAt_writeBits_lo (bw : BitWriter) (sym : Nat)
    (restBits restLen : Nat)
    (h143 : sym ≤ 143) (hrest1 : 1 ≤ restLen)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
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
  have hcode : fixedLitLenCode sym = (sym + 48, 8) := fixedLitLenCode_lo sym h143
  let code := sym + 48
  let bits := reverseBits code 8
  let bitsTot := bits ||| (restBits <<< 8)
  let lenTot := 8 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br8 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 8) bw'.flush
      (flush_size_writeBits_prefix bw bitsTot 8 lenTot (by omega))
      (bitPos_lt_8_writeBits bw bitsTot 8 hbit)
  let br9 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 9) bw'.flush
      (flush_size_writeBits_prefix bw bitsTot 9 lenTot (by omega))
      (bitPos_lt_8_writeBits bw bitsTot 9 hbit)
  have hread9 : br.bitIndex + 9 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 9)
        (hk := by omega) hbit)
  have hbits9 :
      br.readBitsFastU32 9 hread9 = (bitsTot % 2 ^ 9, br9) := by
    simpa [br, bw', br9, lenTot] using
      (readBitsFastU32_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 9)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hread8 : br.bitIndex + 8 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 8)
        (hk := by omega) hbit)
  have hbits8fast :
      br.readBitsFastU32 8 hread8 = (bitsTot % 2 ^ 8, br8) := by
    simpa [br, bw', br8, lenTot] using
      (readBitsFastU32_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 8)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hbits7_eq : bitsTot % 2 ^ 7 = bits % 2 ^ 7 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 7 8 (by decide))
  have hbits7_lt : bitsTot % 2 ^ 7 < fixedLitLenRow7.size := by
    have hlt : bits % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
    simpa [hbits7_eq, fixedLitLenRow7_size, Nat.shiftLeft_eq] using hlt
  have hcode8 : code < 2 ^ 8 := by
    have hlt : code < 192 := by omega
    have hle : 192 ≤ 2 ^ 8 := by decide
    exact lt_of_lt_of_le hlt hle
  have hrev7 : reverseBits (bits % 2 ^ 7) 7 = code >>> 1 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 8) (k := 7) hcode8 (by decide))
  have hrev7' : reverseBits (bitsTot % 2 ^ 7) 7 = code >>> 1 := by
    simpa [hbits7_eq] using hrev7
  have h24 : 24 ≤ code >>> 1 := by
    have hdiv : 24 ≤ code / 2 := by
      have h48 : 48 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2 (by simpa [Nat.mul_comm] using h48)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]'hbits7_lt = none := by
    have h24' : 24 ≤ reverseBits (bitsTot % 2 ^ 7) 7 := by
      simpa [hrev7'] using h24
    exact fixedLitLenRow7_get_none_of_ge (bits := bitsTot % 2 ^ 7) hbits7_lt h24'
  have hrow7? : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some none := by
    simp [hbits7_lt, hrow7]
  have hbits8_eq' : bitsTot % 2 ^ 8 = bits := by
    have hlt : bits < 2 ^ 8 := by simpa [bits] using (reverseBits_lt code 8)
    have hmod' : bits % 2 ^ 8 = bits := Nat.mod_eq_of_lt hlt
    have hmod := mod_two_pow_or_shift bits restBits 8 8 (by decide)
    simpa [bitsTot, hmod'] using hmod
  have hbits8_lt : bitsTot % 2 ^ 8 < fixedLitLenRow8.size := by
    have hlt : bits < 2 ^ 8 := by simpa [bits] using (reverseBits_lt code 8)
    have hlt' : bitsTot % 2 ^ 8 < 2 ^ 8 := by
      simpa [hbits8_eq', bitsTot] using hlt
    simpa [fixedLitLenRow8_size, Nat.shiftLeft_eq] using hlt'
  have hrow8 : fixedLitLenRow8[bitsTot % 2 ^ 8]'hbits8_lt = some sym := by
    have hrow := fixedLitLenCode_row_lo (sym := sym) h143
    simpa [code, bits, hbits8_eq'] using hrow
  have hrow8? : fixedLitLenRow8[bitsTot % 2 ^ 8]? = some (some sym) := by
    simp [hbits8_lt, hrow8]
  have hpeek7 : (bitsTot % 2 ^ 9) % 2 ^ 7 = bitsTot % 2 ^ 7 := by
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 7 ≤ 9))
  have hpeek8 : (bitsTot % 2 ^ 9) % 2 ^ 8 = bitsTot % 2 ^ 8 := by
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 9))
  have hcond9 :
      bw.bitCount + 9 ≤
        (BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit).data.size * 8 := by
    simpa [br, bw', lenTot] using hread9
  have hcond8 :
      bw.bitCount + 8 ≤
        (BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit).data.size * 8 := by
    simpa [br, bw', lenTot] using hread8
  unfold decodeFixedLiteralSymFast9
  simp [hcond9, hcond8, hread9, hbits9, hread8, hbits8fast, hpeek7, hpeek8, hrow7?, hrow8?,
    hcode, code, bits, bitsTot, lenTot, bw', br, br8, br9]

set_option maxRecDepth 100000 in
lemma decodeFixedLiteralSymFast9_readerAt_writeBits_mid (bw : BitWriter) (sym : Nat)
    (restBits restLen : Nat)
    (h144 : 144 ≤ sym) (h255 : sym ≤ 255)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
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
  have hcode : fixedLitLenCode sym = (sym - 144 + 400, 9) :=
    fixedLitLenCode_mid sym h144 h255
  let code := sym - 144 + 400
  let bits := reverseBits code 9
  let bitsTot := bits ||| (restBits <<< 9)
  let lenTot := 9 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br9 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 9) bw'.flush
      (flush_size_writeBits_prefix bw bitsTot 9 lenTot (by omega))
      (bitPos_lt_8_writeBits bw bitsTot 9 hbit)
  have hread9 : br.bitIndex + 9 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 9)
        (hk := by omega) hbit)
  have hbits9 :
      br.readBitsFastU32 9 hread9 = (bitsTot % 2 ^ 9, br9) := by
    simpa [br, bw', br9, lenTot] using
      (readBitsFastU32_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 9)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hbits7_eq : bitsTot % 2 ^ 7 = bits % 2 ^ 7 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 7 9 (by decide))
  have hbits7_lt : bitsTot % 2 ^ 7 < fixedLitLenRow7.size := by
    have hlt : bits % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
    simpa [hbits7_eq, fixedLitLenRow7_size, Nat.shiftLeft_eq] using hlt
  have hcode9 : code < 2 ^ 9 := by
    have hlt : code < 512 := by omega
    have hle : 512 ≤ 2 ^ 9 := by decide
    exact lt_of_lt_of_le hlt hle
  have hrev7 : reverseBits (bits % 2 ^ 7) 7 = code >>> 2 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 9) (k := 7) hcode9 (by decide))
  have hrev7' : reverseBits (bitsTot % 2 ^ 7) 7 = code >>> 2 := by
    simpa [hbits7_eq] using hrev7
  have h24 : 24 ≤ code >>> 2 := by
    have hdiv : 24 ≤ code / 4 := by
      have h96 : 96 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (4 : Nat))).2 (by simpa [Nat.mul_comm] using h96)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]'hbits7_lt = none := by
    have h24' : 24 ≤ reverseBits (bitsTot % 2 ^ 7) 7 := by simpa [hrev7'] using h24
    exact fixedLitLenRow7_get_none_of_ge (bits := bitsTot % 2 ^ 7) hbits7_lt h24'
  have hrow7? : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some none := by
    simp [hbits7_lt, hrow7]
  have hbits8_eq' : bitsTot % 2 ^ 8 = bits % 2 ^ 8 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 8 9 (by decide))
  have hbits8_lt : bitsTot % 2 ^ 8 < fixedLitLenRow8.size := by
    have hlt : bits % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
    simpa [hbits8_eq', fixedLitLenRow8_size, Nat.shiftLeft_eq] using hlt
  have hrev8 : reverseBits (bits % 2 ^ 8) 8 = code >>> 1 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 9) (k := 8) hcode9 (by decide))
  have hrev8' : reverseBits (bitsTot % 2 ^ 8) 8 = code >>> 1 := by
    simpa [hbits8_eq'] using hrev8
  have h200 : 200 ≤ code >>> 1 := by
    have hdiv : 200 ≤ code / 2 := by
      have h400 : 400 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2 (by simpa [Nat.mul_comm] using h400)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow8 : fixedLitLenRow8[bitsTot % 2 ^ 8]'hbits8_lt = none := by
    have h200' : 200 ≤ reverseBits (bitsTot % 2 ^ 8) 8 := by simpa [hrev8'] using h200
    exact fixedLitLenRow8_get_none_of_ge (bits := bitsTot % 2 ^ 8) hbits8_lt h200'
  have hrow8? : fixedLitLenRow8[bitsTot % 2 ^ 8]? = some none := by
    simp [hbits8_lt, hrow8]
  have hbits9_eq' : bitsTot % 2 ^ 9 = bits := by
    have hmod := mod_two_pow_or_shift bits restBits 9 9 (by decide)
    have hlt : bits < 2 ^ 9 := by simpa [bits] using (reverseBits_lt code 9)
    have hmod' : bits % 2 ^ 9 = bits := Nat.mod_eq_of_lt hlt
    simpa [bitsTot, hmod'] using hmod
  have hbits9_lt : bitsTot % 2 ^ 9 < fixedLitLenRow9.size := by
    have hlt : bits < 2 ^ 9 := by simpa [bits] using (reverseBits_lt code 9)
    simpa [hbits9_eq', fixedLitLenRow9_size, Nat.shiftLeft_eq] using hlt
  have hrow9 : fixedLitLenRow9[bitsTot % 2 ^ 9]'hbits9_lt = some sym := by
    have hrow := fixedLitLenCode_row_mid (sym := sym) h144 h255
    simpa [code, bits, hbits9_eq'] using hrow
  have hrow9? : fixedLitLenRow9[bitsTot % 2 ^ 9]? = some (some sym) := by
    simp [hbits9_lt, hrow9]
  have hpeek7 : (bitsTot % 2 ^ 9) % 2 ^ 7 = bitsTot % 2 ^ 7 := by
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 7 ≤ 9))
  have hpeek8 : (bitsTot % 2 ^ 9) % 2 ^ 8 = bitsTot % 2 ^ 8 := by
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 9))
  have hcond9 :
      bw.bitCount + 9 ≤
        (BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit).data.size * 8 := by
    simpa [br, bw', lenTot] using hread9
  unfold decodeFixedLiteralSymFast9
  simp [hcond9, hread9, hbits9, hpeek7, hpeek8, hrow7?, hrow8?, hrow9?, hcode, code, bits, bitsTot, lenTot, bw', br, br9]

set_option maxRecDepth 100000 in
lemma decodeFixedLiteralSymFast9_readerAt_writeBits_hi (bw : BitWriter) (sym : Nat)
    (restBits restLen : Nat)
    (h256 : 256 ≤ sym) (h279 : sym ≤ 279) (hrest2 : 2 ≤ restLen)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
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
  have hcode : fixedLitLenCode sym = (sym - 256, 7) :=
    fixedLitLenCode_hi sym h256 h279
  let code := sym - 256
  let bits := reverseBits code 7
  let bitsTot := bits ||| (restBits <<< 7)
  let lenTot := 7 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br7 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 7) bw'.flush
      (flush_size_writeBits_prefix bw bitsTot 7 lenTot (by omega))
      (bitPos_lt_8_writeBits bw bitsTot 7 hbit)
  let br9 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 9) bw'.flush
      (flush_size_writeBits_prefix bw bitsTot 9 lenTot (by omega))
      (bitPos_lt_8_writeBits bw bitsTot 9 hbit)
  have hread9 : br.bitIndex + 9 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 9)
        (hk := by omega) hbit)
  have hbits9 :
      br.readBitsFastU32 9 hread9 = (bitsTot % 2 ^ 9, br9) := by
    simpa [br, bw', br9, lenTot] using
      (readBitsFastU32_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 9)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hread7 : br.bitIndex + 7 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 7)
        (hk := by omega) hbit)
  have hbits7fast :
      br.readBitsFastU32 7 hread7 = (bitsTot % 2 ^ 7, br7) := by
    simpa [br, bw', br7, lenTot] using
      (readBitsFastU32_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 7)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hbits7_eq : bitsTot % 2 ^ 7 = bits := by
    have hmod := mod_two_pow_or_shift bits restBits 7 7 (by decide)
    have hlt : bits < 2 ^ 7 := by simpa [bits] using (reverseBits_lt code 7)
    have hmod' : bits % 2 ^ 7 = bits := Nat.mod_eq_of_lt hlt
    simpa [bitsTot, hmod'] using hmod
  have hbits7_lt : bitsTot % 2 ^ 7 < fixedLitLenRow7.size := by
    have hlt : bits < 2 ^ 7 := by simpa [bits] using (reverseBits_lt code 7)
    simpa [hbits7_eq, fixedLitLenRow7_size, Nat.shiftLeft_eq] using hlt
  have hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]'hbits7_lt = some sym := by
    have hrow := fixedLitLenCode_row_hi (sym := sym) h256 h279
    simpa [code, bits, hbits7_eq] using hrow
  have hrow7? : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some (some sym) := by
    simp [hbits7_lt, hrow7]
  have hpeek7 : (bitsTot % 2 ^ 9) % 2 ^ 7 = bitsTot % 2 ^ 7 := by
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 7 ≤ 9))
  have hcond9 :
      bw.bitCount + 9 ≤
        (BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit).data.size * 8 := by
    simpa [br, bw', lenTot] using hread9
  have hcond7 :
      bw.bitCount + 7 ≤
        (BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit).data.size * 8 := by
    simpa [br, bw', lenTot] using hread7
  unfold decodeFixedLiteralSymFast9
  simp [hcond9, hcond7, hread9, hbits9, hread7, hbits7fast, hpeek7, hrow7?, hcode, code, bits, bitsTot, lenTot, bw', br, br7,
    br9]

set_option maxRecDepth 100000 in
lemma decodeFixedLiteralSymFast9_readerAt_writeBits_hi2 (bw : BitWriter) (sym : Nat)
    (restBits restLen : Nat)
    (h280 : 280 ≤ sym) (h287 : sym ≤ 287) (hrest1 : 1 ≤ restLen)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
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
  have hcode : fixedLitLenCode sym = (sym - 280 + 192, 8) :=
    fixedLitLenCode_hi2 sym h280 h287
  let code := sym - 280 + 192
  let bits := reverseBits code 8
  let bitsTot := bits ||| (restBits <<< 8)
  let lenTot := 8 + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br8 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 8) bw'.flush
      (flush_size_writeBits_prefix bw bitsTot 8 lenTot (by omega))
      (bitPos_lt_8_writeBits bw bitsTot 8 hbit)
  let br9 :=
    BitWriter.readerAt (BitWriter.writeBits bw bitsTot 9) bw'.flush
      (flush_size_writeBits_prefix bw bitsTot 9 lenTot (by omega))
      (bitPos_lt_8_writeBits bw bitsTot 9 hbit)
  have hread9 : br.bitIndex + 9 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 9)
        (hk := by omega) hbit)
  have hbits9 :
      br.readBitsFastU32 9 hread9 = (bitsTot % 2 ^ 9, br9) := by
    simpa [br, bw', br9, lenTot] using
      (readBitsFastU32_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 9)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hread8 : br.bitIndex + 8 ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := 8)
        (hk := by omega) hbit)
  have hbits8fast :
      br.readBitsFastU32 8 hread8 = (bitsTot % 2 ^ 8, br8) := by
    simpa [br, bw', br8, lenTot] using
      (readBitsFastU32_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot) (k := 8)
        (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hbits7_eq : bitsTot % 2 ^ 7 = bits % 2 ^ 7 := by
    simpa [bitsTot] using (mod_two_pow_or_shift bits restBits 7 8 (by decide))
  have hbits7_lt : bitsTot % 2 ^ 7 < fixedLitLenRow7.size := by
    have hlt : bits % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
    simpa [hbits7_eq, fixedLitLenRow7_size, Nat.shiftLeft_eq] using hlt
  have hcode8 : code < 2 ^ 8 := by
    have hlt : code < 200 := by omega
    have hle : 200 ≤ 2 ^ 8 := by decide
    exact lt_of_lt_of_le hlt hle
  have hrev7 : reverseBits (bits % 2 ^ 7) 7 = code >>> 1 := by
    simpa [bits] using
      (reverseBits_prefix_shift (code := code) (len := 8) (k := 7) hcode8 (by decide))
  have hrev7' : reverseBits (bitsTot % 2 ^ 7) 7 = code >>> 1 := by
    simpa [hbits7_eq] using hrev7
  have h24 : 24 ≤ code >>> 1 := by
    have hdiv : 24 ≤ code / 2 := by
      have h48 : 48 ≤ code := by omega
      exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : Nat))).2 (by simpa [Nat.mul_comm] using h48)
    simpa [Nat.shiftRight_eq_div_pow] using hdiv
  have hrow7 : fixedLitLenRow7[bitsTot % 2 ^ 7]'hbits7_lt = none := by
    have h24' : 24 ≤ reverseBits (bitsTot % 2 ^ 7) 7 := by simpa [hrev7'] using h24
    exact fixedLitLenRow7_get_none_of_ge (bits := bitsTot % 2 ^ 7) hbits7_lt h24'
  have hrow7? : fixedLitLenRow7[bitsTot % 2 ^ 7]? = some none := by
    simp [hbits7_lt, hrow7]
  have hbits8_eq' : bitsTot % 2 ^ 8 = bits := by
    have hmod := mod_two_pow_or_shift bits restBits 8 8 (by decide)
    have hlt : bits < 2 ^ 8 := by simpa [bits] using (reverseBits_lt code 8)
    have hmod' : bits % 2 ^ 8 = bits := Nat.mod_eq_of_lt hlt
    simpa [bitsTot, hmod'] using hmod
  have hbits8_lt : bitsTot % 2 ^ 8 < fixedLitLenRow8.size := by
    have hlt : bits < 2 ^ 8 := by simpa [bits] using (reverseBits_lt code 8)
    simpa [hbits8_eq', fixedLitLenRow8_size, Nat.shiftLeft_eq] using hlt
  have hrow8 : fixedLitLenRow8[bitsTot % 2 ^ 8]'hbits8_lt = some sym := by
    have hrow := fixedLitLenCode_row_hi2 (sym := sym) h280 h287
    simpa [code, bits, hbits8_eq'] using hrow
  have hrow8? : fixedLitLenRow8[bitsTot % 2 ^ 8]? = some (some sym) := by
    simp [hbits8_lt, hrow8]
  have hpeek7 : (bitsTot % 2 ^ 9) % 2 ^ 7 = bitsTot % 2 ^ 7 := by
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 7 ≤ 9))
  have hpeek8 : (bitsTot % 2 ^ 9) % 2 ^ 8 = bitsTot % 2 ^ 8 := by
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 9))
  have hcond9 :
      bw.bitCount + 9 ≤
        (BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit).data.size * 8 := by
    simpa [br, bw', lenTot] using hread9
  have hcond8 :
      bw.bitCount + 8 ≤
        (BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit).data.size * 8 := by
    simpa [br, bw', lenTot] using hread8
  unfold decodeFixedLiteralSymFast9
  simp [hcond9, hcond8, hread9, hbits9, hread8, hbits8fast, hpeek7, hpeek8, hrow7?, hrow8?, hcode, code, bits,
    bitsTot, lenTot, bw', br, br8, br9]

lemma decodeFixedLiteralSymFast9_readerAt_writeBits_matchSym (bw : BitWriter) (sym : Nat)
    (restBits restLen : Nat) (hsym : 257 ≤ sym ∧ sym ≤ 285) (hrest2 : 2 ≤ restLen)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
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
  rcases hsym with ⟨h257, h285⟩
  by_cases h279 : sym ≤ 279
  · exact decodeFixedLiteralSymFast9_readerAt_writeBits_hi (bw := bw) (sym := sym)
      (restBits := restBits) (restLen := restLen) (by omega) h279 hrest2 hbit hcur
  · have h280 : 280 ≤ sym := by omega
    exact decodeFixedLiteralSymFast9_readerAt_writeBits_hi2 (bw := bw) (sym := sym)
      (restBits := restBits) (restLen := restLen) h280 (by omega) (by omega) hbit hcur

lemma decodeFixedLiteralSymFast9_readerAt_writeBits
    (bw : BitWriter) (sym : Nat) (restBits restLen : Nat)
    (hsym : sym < 288) (hrest2 : 2 ≤ restLen)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
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
  classical
  by_cases h143 : sym ≤ 143
  · exact decodeFixedLiteralSymFast9_readerAt_writeBits_lo (bw := bw) (sym := sym)
      (restBits := restBits) (restLen := restLen) h143 (by omega) hbit hcur
  · have h144 : 144 ≤ sym := by omega
    by_cases h255 : sym ≤ 255
    · exact decodeFixedLiteralSymFast9_readerAt_writeBits_mid (bw := bw) (sym := sym)
        (restBits := restBits) (restLen := restLen) h144 h255 hbit hcur
    · have h256 : 256 ≤ sym := by omega
      by_cases h279 : sym ≤ 279
      · exact decodeFixedLiteralSymFast9_readerAt_writeBits_hi (bw := bw) (sym := sym)
          (restBits := restBits) (restLen := restLen) h256 h279 hrest2 hbit hcur
      · have h280 : 280 ≤ sym := by omega
        have h287 : sym ≤ 287 := by omega
        exact decodeFixedLiteralSymFast9_readerAt_writeBits_hi2 (bw := bw) (sym := sym)
          (restBits := restBits) (restLen := restLen) h280 h287 (by omega) hbit hcur

-- The runtime match-length encoder metadata agrees with the DEFLATE length tables.
set_option maxRecDepth 100000 in
lemma fixedLenMatchInfo_spec_get! (len : Nat) (hlo : 3 ≤ len) (hhi : len ≤ 258) :
    match fixedLenMatchInfo len with
    | (sym, extraBits, extraLen) =>
        257 ≤ sym ∧ sym ≤ 285 ∧
          extraLen = lengthExtra[sym - 257]! ∧
          lengthBases[sym - 257]! + extraBits = len ∧
          extraBits < 2 ^ extraLen := by
  have hall :
      ∀ n : Fin 256,
        match fixedLenMatchInfo (n.1 + 3) with
        | (sym, extraBits, extraLen) =>
            257 ≤ sym ∧ sym ≤ 285 ∧
              extraLen = lengthExtra[sym - 257]! ∧
              lengthBases[sym - 257]! + extraBits = (n.1 + 3) ∧
              extraBits < 2 ^ extraLen := by
    decide
  let n : Fin 256 := ⟨len - 3, by omega⟩
  have hlen : len = n.1 + 3 := by
    have hsub : (len - 3) + 3 = len := Nat.sub_add_cancel hlo
    simpa [n] using hsub.symm
  simpa [hlen] using hall n

lemma array_getInternal_eq_get! {α : Type u} [Inhabited α]
    (arr : Array α) (i : Nat) (h : i < arr.size) :
    Array.getInternal arr i h = arr[i]! := by
  simp [Array.getInternal, getElem!_pos, h]

set_option maxRecDepth 100000 in
-- Internal-table version of `fixedLenMatchInfo_spec_get!`, suitable for `decodeLength`.
lemma fixedLenMatchInfo_spec_internal (len : Nat) (hlo : 3 ≤ len) (hhi : len ≤ 258) :
    match fixedLenMatchInfo len with
    | (sym, extraBits, extraLen) =>
        ∃ _hsym : 257 ≤ sym ∧ sym ≤ 285,
          ∃ hidxBase : sym - 257 < lengthBases.size,
            ∃ hidxExtra : sym - 257 < lengthExtra.size,
              extraLen = Array.getInternal lengthExtra (sym - 257) hidxExtra ∧
              Array.getInternal lengthBases (sym - 257) hidxBase + extraBits = len ∧
              extraBits < 2 ^ extraLen := by
  rcases hfixed : fixedLenMatchInfo len with ⟨sym, extraBits, extraLen⟩
  have hspec := fixedLenMatchInfo_spec_get! len hlo hhi
  have hspec' :
      257 ≤ sym ∧ sym ≤ 285 ∧
        extraLen = lengthExtra[sym - 257]! ∧
        lengthBases[sym - 257]! + extraBits = len ∧
        extraBits < 2 ^ extraLen := by
    simpa [hfixed] using hspec
  rcases hspec' with ⟨hsymLo, hrest⟩
  rcases hrest with ⟨hsymHi, hrest⟩
  rcases hrest with ⟨hextraBang, hrest⟩
  rcases hrest with ⟨hbaseBang, hbitsLt⟩
  let hsym : 257 ≤ sym ∧ sym ≤ 285 := ⟨hsymLo, hsymHi⟩
  have hidxlt : sym - 257 < 29 := by omega
  have hidxBase : sym - 257 < lengthBases.size := by
    have hsize : lengthBases.size = 29 := by decide
    simpa [hsize] using hidxlt
  have hidxExtra : sym - 257 < lengthExtra.size := by
    have hsize : lengthExtra.size = 29 := by decide
    simpa [hsize] using hidxlt
  refine ⟨hsym, hidxBase, hidxExtra, ?_, ?_, hbitsLt⟩
  · calc
      extraLen = lengthExtra[sym - 257]! := hextraBang
      _ = Array.getInternal lengthExtra (sym - 257) hidxExtra := by
            symm
            exact array_getInternal_eq_get! _ _ _
  · calc
      Array.getInternal lengthBases (sym - 257) hidxBase + extraBits
          = lengthBases[sym - 257]! + extraBits := by
              rw [array_getInternal_eq_get!]
      _ = len := hbaseBang

lemma writeFixedMatchDist1Fast_eq_writeBits_chain (bw : BitWriter) (matchLen : Nat)
    (hlen : 3 ≤ matchLen ∧ matchLen ≤ 258) :
    let info := fixedLenMatchInfo matchLen
    let sym := info.1
    let extraBits := info.2.1
    let extraLen := info.2.2
    BitWriter.writeFixedMatchDist1Fast bw matchLen =
      let codeLen := fixedLitLenCode sym
      let symBits := reverseBits codeLen.1 codeLen.2
      let bw1 := BitWriter.writeBits bw symBits codeLen.2
      let bw2 := BitWriter.writeBits bw1 extraBits extraLen
      BitWriter.writeBits bw2 0 5 := by
  have hinfo := fixedLenMatchInfo_spec_get! matchLen hlen.1 hlen.2
  have hsym : (fixedLenMatchInfo matchLen).1 < 288 := by
    omega
  unfold BitWriter.writeFixedMatchDist1Fast
  simp [fixedLitLenRevCodeFast_eq, hsym]

lemma chooseFixedMatchChunkLen_bounds (remaining : Nat) (hrem : 3 ≤ remaining) :
    3 ≤ chooseFixedMatchChunkLen remaining ∧
    chooseFixedMatchChunkLen remaining ≤ 258 ∧
    chooseFixedMatchChunkLen remaining ≤ remaining := by
  by_cases hgt : remaining > 258
  · have hge258 : 258 ≤ remaining := Nat.le_of_lt hgt
    by_cases hr1 : (remaining % 258 == 1)
    · refine ⟨by simp [chooseFixedMatchChunkLen, hgt, hr1], by simp [chooseFixedMatchChunkLen, hgt, hr1], ?_⟩
      have h256 : chooseFixedMatchChunkLen remaining = 256 := by
        simp [chooseFixedMatchChunkLen, hgt, hr1]
      omega
    · by_cases hr2 : (remaining % 258 == 2)
      · refine ⟨by simp [chooseFixedMatchChunkLen, hgt, hr1, hr2], by simp [chooseFixedMatchChunkLen, hgt, hr1, hr2], ?_⟩
        have h257 : chooseFixedMatchChunkLen remaining = 257 := by
          simp [chooseFixedMatchChunkLen, hgt, hr1, hr2]
        omega
      · refine ⟨by simp [chooseFixedMatchChunkLen, hgt, hr1, hr2], by simp [chooseFixedMatchChunkLen, hgt, hr1, hr2], ?_⟩
        have h258 : chooseFixedMatchChunkLen remaining = 258 := by
          simp [chooseFixedMatchChunkLen, hgt, hr1, hr2]
        omega
  · have hle258 : remaining ≤ 258 := Nat.le_of_not_gt hgt
    simp [chooseFixedMatchChunkLen, hgt, hrem, hle258]

lemma chooseFixedMatchChunkLen_sub_lt (remaining : Nat) (hrem : 3 ≤ remaining) :
    remaining - chooseFixedMatchChunkLen remaining < remaining := by
  have hbounds := chooseFixedMatchChunkLen_bounds remaining hrem
  have hchunk_ge3 : 3 ≤ chooseFixedMatchChunkLen remaining := hbounds.1
  have hchunk_pos : 0 < chooseFixedMatchChunkLen remaining := by
    exact lt_of_lt_of_le (by decide : 0 < 3) hchunk_ge3
  exact Nat.sub_lt (show 0 < remaining by omega) hchunk_pos

lemma writeBits_dist1Prefix_concat (bw : BitWriter) (tailBits tailLen : Nat) :
    let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
    let bwAfter := BitWriter.writeBits bw distBitsTot 5
    BitWriter.writeBits bw distBitsTot (5 + tailLen) =
      BitWriter.writeBits bwAfter tailBits tailLen := by
  let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
  have hmod0 : distBitsTot % 2 ^ 5 = 0 := by
    have h := mod_two_pow_or_shift (a := 0) (b := tailBits) (k := 5) (len := 5) (hk := by decide)
    simpa [distBitsTot] using h
  have hprefix0 : BitWriter.writeBits bw distBitsTot 5 = BitWriter.writeBits bw 0 5 := by
    calc
      BitWriter.writeBits bw distBitsTot 5 = BitWriter.writeBits bw (distBitsTot % 2 ^ 5) 5 := by
        simpa using (writeBits_mod bw distBitsTot 5)
      _ = BitWriter.writeBits bw 0 5 := by
        simp [hmod0]
  have hconcat :
      BitWriter.writeBits bw distBitsTot (5 + tailLen) =
        BitWriter.writeBits (BitWriter.writeBits bw 0 5) tailBits tailLen := by
    have hbits : (0 : Nat) < 2 ^ 5 := by decide
    simpa [distBitsTot] using (writeBits_concat bw 0 tailBits 5 tailLen hbits)
  calc
    BitWriter.writeBits bw distBitsTot (5 + tailLen)
        = BitWriter.writeBits (BitWriter.writeBits bw 0 5) tailBits tailLen := hconcat
    _ = BitWriter.writeBits (BitWriter.writeBits bw distBitsTot 5) tailBits tailLen := by
          rw [hprefix0]

lemma shiftLeft_add_rev (x a b : Nat) : (x <<< a) <<< b = x <<< (a + b) := by
  simpa using (Nat.shiftLeft_add x a b).symm

lemma readerAt_writeBits_dist1Prefix_concat
    (bw2 : BitWriter) (tailBits tailLen : Nat)
    (hbit2 : bw2.bitPos < 8) :
    let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
    let distLenTot := 5 + tailLen
    let bwChunk := BitWriter.writeBits bw2 distBitsTot 5
    let bwDistAll := BitWriter.writeBits bw2 distBitsTot distLenTot
    BitWriter.readerAt bwChunk bwDistAll.flush
      (by
        have hk : 5 ≤ distLenTot := by omega
        simpa [distLenTot] using (flush_size_writeBits_prefix bw2 distBitsTot 5 distLenTot hk))
      (bitPos_lt_8_writeBits bw2 distBitsTot 5 hbit2)
    =
    BitWriter.readerAt bwChunk (BitWriter.writeBits bwChunk tailBits tailLen).flush
      (flush_size_writeBits_le bwChunk tailBits tailLen)
      (bitPos_lt_8_writeBits bw2 distBitsTot 5 hbit2) := by
  let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
  let distLenTot := 5 + tailLen
  let bwChunk := BitWriter.writeBits bw2 distBitsTot 5
  let bwDistAll := BitWriter.writeBits bw2 distBitsTot distLenTot
  have hbw : bwDistAll = BitWriter.writeBits bwChunk tailBits tailLen := by
    simpa [bwDistAll, bwChunk, distBitsTot, distLenTot] using
      (writeBits_dist1Prefix_concat bw2 tailBits tailLen)
  apply BitReader.ext
  · simpa [bwDistAll, bwChunk, distBitsTot, distLenTot, BitWriter.readerAt] using
      congrArg BitWriter.flush hbw
  · simp [BitWriter.readerAt]
  · simp [BitWriter.readerAt]

def dist1ChunkLoopOut (out : ByteArray) (remaining : Nat) : ByteArray :=
  if _h : 3 ≤ remaining then
    dist1ChunkLoopOut
      (pushRepeat out (out.get! (out.size - 1)) (chooseFixedMatchChunkLen remaining))
      (remaining - chooseFixedMatchChunkLen remaining)
  else
    out
termination_by remaining
decreasing_by
  exact chooseFixedMatchChunkLen_sub_lt remaining _h

def dist1ChunkLoopSteps (remaining : Nat) : Nat :=
  if _h : 3 ≤ remaining then
    1 + dist1ChunkLoopSteps (remaining - chooseFixedMatchChunkLen remaining)
  else
    0
termination_by remaining
decreasing_by
  exact chooseFixedMatchChunkLen_sub_lt remaining _h

def dist1ChunkLoopBits (remaining : Nat) : Nat × Nat :=
  if _h : 3 ≤ remaining then
    let chunk := chooseFixedMatchChunkLen remaining
    let info := fixedLenMatchInfo chunk
    let sym := info.1
    let extraBits := info.2.1
    let extraLen := info.2.2
    let codeLen := fixedLitLenCode sym
    let symBits := reverseBits codeLen.1 codeLen.2
    let distBitsTot := (0 : Nat)
    let distLenTot := 5
    let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
    let lenLenTot := extraLen + distLenTot
    let matchBits := symBits ||| (lenBitsTot <<< codeLen.2)
    let matchLen := codeLen.2 + lenLenTot
    let rest := dist1ChunkLoopBits (remaining - chunk)
    (matchBits ||| (rest.1 <<< matchLen), matchLen + rest.2)
  else
    (0, 0)
termination_by remaining
decreasing_by
  exact chooseFixedMatchChunkLen_sub_lt remaining _h

lemma dist1ChunkLoopOut_unfold (out : ByteArray) (remaining : Nat) :
    dist1ChunkLoopOut out remaining =
      (if _h : 3 ≤ remaining then
        dist1ChunkLoopOut
          (pushRepeat out (out.get! (out.size - 1)) (chooseFixedMatchChunkLen remaining))
          (remaining - chooseFixedMatchChunkLen remaining)
      else
        out) := by
  exact dist1ChunkLoopOut.eq_1 (out := out) (remaining := remaining)

lemma dist1ChunkLoopSteps_unfold (remaining : Nat) :
    dist1ChunkLoopSteps remaining =
      (if _h : 3 ≤ remaining then
        1 + dist1ChunkLoopSteps (remaining - chooseFixedMatchChunkLen remaining)
      else
        0) := by
  exact dist1ChunkLoopSteps.eq_1 (remaining := remaining)

lemma dist1ChunkLoopBits_unfold (remaining : Nat) :
    dist1ChunkLoopBits remaining =
      (if _h : 3 ≤ remaining then
        let chunk := chooseFixedMatchChunkLen remaining
        let info := fixedLenMatchInfo chunk
        let sym := info.1
        let extraBits := info.2.1
        let extraLen := info.2.2
        let codeLen := fixedLitLenCode sym
        let symBits := reverseBits codeLen.1 codeLen.2
        let distBitsTot := (0 : Nat)
        let distLenTot := 5
        let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
        let lenLenTot := extraLen + distLenTot
        let matchBits := symBits ||| (lenBitsTot <<< codeLen.2)
        let matchLen := codeLen.2 + lenLenTot
        let rest := dist1ChunkLoopBits (remaining - chunk)
        (matchBits ||| (rest.1 <<< matchLen), matchLen + rest.2)
      else
        (0, 0)) := by
  exact dist1ChunkLoopBits.eq_1 (remaining := remaining)

lemma dist1ChunkLoopOut_of_ge3 (out : ByteArray) (remaining : Nat) (h : 3 ≤ remaining) :
    dist1ChunkLoopOut out remaining =
      dist1ChunkLoopOut
        (pushRepeat out (out.get! (out.size - 1)) (chooseFixedMatchChunkLen remaining))
        (remaining - chooseFixedMatchChunkLen remaining) := by
  rw [dist1ChunkLoopOut_unfold]
  simp [h]

lemma dist1ChunkLoopOut_of_lt3 (out : ByteArray) (remaining : Nat) (h : ¬ 3 ≤ remaining) :
    dist1ChunkLoopOut out remaining = out := by
  rw [dist1ChunkLoopOut_unfold]
  simp [h]

lemma dist1ChunkLoopSteps_of_ge3 (remaining : Nat) (h : 3 ≤ remaining) :
    dist1ChunkLoopSteps remaining =
      1 + dist1ChunkLoopSteps (remaining - chooseFixedMatchChunkLen remaining) := by
  rw [dist1ChunkLoopSteps_unfold]
  simp [h]

lemma dist1ChunkLoopSteps_of_lt3 (remaining : Nat) (h : ¬ 3 ≤ remaining) :
    dist1ChunkLoopSteps remaining = 0 := by
  rw [dist1ChunkLoopSteps_unfold]
  simp [h]

lemma dist1ChunkLoopBits_of_ge3 (remaining : Nat) (h : 3 ≤ remaining) :
    let chunk := chooseFixedMatchChunkLen remaining
    let info := fixedLenMatchInfo chunk
    let sym := info.1
    let extraBits := info.2.1
    let extraLen := info.2.2
    let codeLen := fixedLitLenCode sym
    let symBits := reverseBits codeLen.1 codeLen.2
    let distBitsTot := (0 : Nat)
    let distLenTot := 5
    let lenBitsTot := extraBits ||| (distBitsTot <<< extraLen)
    let lenLenTot := extraLen + distLenTot
    let matchBits := symBits ||| (lenBitsTot <<< codeLen.2)
    let matchLen := codeLen.2 + lenLenTot
    let rest := dist1ChunkLoopBits (remaining - chunk)
    dist1ChunkLoopBits remaining = (matchBits ||| (rest.1 <<< matchLen), matchLen + rest.2) := by
  rw [dist1ChunkLoopBits_unfold]
  simp [h]

lemma dist1ChunkLoopBits_of_lt3 (remaining : Nat) (h : ¬ 3 ≤ remaining) :
    dist1ChunkLoopBits remaining = (0, 0) := by
  rw [dist1ChunkLoopBits_unfold]
  simp [h]

def dist1ChunkLoopBitsTail (remaining tailBits tailLen : Nat) : Nat × Nat :=
  if _h : 3 ≤ remaining then
    let chunk := chooseFixedMatchChunkLen remaining
    let rest := dist1ChunkLoopBitsTail (remaining - chunk) tailBits tailLen
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
    let bitsTot := symBits ||| (lenBitsTot <<< codeLen.2)
    let lenTot := codeLen.2 + lenLenTot
    (bitsTot, lenTot)
  else
    (tailBits, tailLen)
termination_by remaining
decreasing_by
  exact chooseFixedMatchChunkLen_sub_lt remaining _h

lemma dist1ChunkLoopBitsTail_unfold (remaining tailBits tailLen : Nat) :
    dist1ChunkLoopBitsTail remaining tailBits tailLen =
      (if _h : 3 ≤ remaining then
        let chunk := chooseFixedMatchChunkLen remaining
        let rest := dist1ChunkLoopBitsTail (remaining - chunk) tailBits tailLen
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
        let bitsTot := symBits ||| (lenBitsTot <<< codeLen.2)
        let lenTot := codeLen.2 + lenLenTot
        (bitsTot, lenTot)
      else
        (tailBits, tailLen)) := by
  exact dist1ChunkLoopBitsTail.eq_1 (remaining := remaining) (tailBits := tailBits) (tailLen := tailLen)

lemma dist1ChunkLoopBitsTail_of_ge3 (remaining tailBits tailLen : Nat) (h : 3 ≤ remaining) :
    let chunk := chooseFixedMatchChunkLen remaining
    let rest := dist1ChunkLoopBitsTail (remaining - chunk) tailBits tailLen
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
    let bitsTot := symBits ||| (lenBitsTot <<< codeLen.2)
    let lenTot := codeLen.2 + lenLenTot
    dist1ChunkLoopBitsTail remaining tailBits tailLen = (bitsTot, lenTot) := by
  rw [dist1ChunkLoopBitsTail_unfold]
  simp [h]

lemma dist1ChunkLoopBitsTail_of_lt3 (remaining tailBits tailLen : Nat) (h : ¬ 3 ≤ remaining) :
    dist1ChunkLoopBitsTail remaining tailBits tailLen = (tailBits, tailLen) := by
  rw [dist1ChunkLoopBitsTail_unfold]
  simp [h]

lemma dist1ChunkLoopOut_pos (out : ByteArray) (remaining : Nat) (hout : 0 < out.size) :
    0 < (dist1ChunkLoopOut out remaining).size := by
  revert out hout
  refine Nat.strong_induction_on remaining ?_
  intro remaining ih out hout
  rw [dist1ChunkLoopOut_unfold]
  by_cases h : 3 ≤ remaining
  · simp [h]
    have hout' : 0 < (pushRepeat out (out.get! (out.size - 1)) (chooseFixedMatchChunkLen remaining)).size := by
      exact pushRepeat_pos out (out.get! (out.size - 1)) (chooseFixedMatchChunkLen remaining) hout
    exact ih (remaining - chooseFixedMatchChunkLen remaining)
      (chooseFixedMatchChunkLen_sub_lt remaining h)
      (pushRepeat out (out.get! (out.size - 1)) (chooseFixedMatchChunkLen remaining)) hout'
  · simp [h, hout]

lemma dist1ChunkLoopOut_last_eq
    (out : ByteArray) (remaining : Nat) (b : UInt8)
    (hout : 0 < out.size)
    (hlast : out.get! (out.size - 1) = b) :
    (dist1ChunkLoopOut out remaining).get! ((dist1ChunkLoopOut out remaining).size - 1) = b := by
  revert out hout hlast
  refine Nat.strong_induction_on remaining ?_
  intro remaining ih out hout hlast
  rw [dist1ChunkLoopOut_unfold]
  by_cases h : 3 ≤ remaining
  · simp [h]
    let chunk := chooseFixedMatchChunkLen remaining
    let out' := pushRepeat out (out.get! (out.size - 1)) chunk
    have hout' : 0 < out'.size := by
      dsimp [out']
      exact pushRepeat_pos out (out.get! (out.size - 1)) chunk hout
    have hlast' : out'.get! (out'.size - 1) = b := by
      have hpushLast :=
        pushRepeat_last_get! out (out.get! (out.size - 1)) b chunk hout hlast
      by_cases hchunk0 : chunk = 0
      · have hcontra : False := by
          have hbounds := chooseFixedMatchChunkLen_bounds remaining h
          omega
        exact False.elim hcontra
      · simpa [out', hchunk0, hlast] using hpushLast
    exact ih (remaining - chunk)
      (by simpa [chunk] using (chooseFixedMatchChunkLen_sub_lt remaining h))
      out' hout' hlast'
  · simp [h, hlast]

def dist1ChunkLoopRem (remaining : Nat) : Nat :=
  if _h : 3 ≤ remaining then
    dist1ChunkLoopRem (remaining - chooseFixedMatchChunkLen remaining)
  else
    remaining
termination_by remaining
decreasing_by
  exact chooseFixedMatchChunkLen_sub_lt remaining _h

lemma dist1ChunkLoopRem_unfold (remaining : Nat) :
    dist1ChunkLoopRem remaining =
      (if _h : 3 ≤ remaining then
        dist1ChunkLoopRem (remaining - chooseFixedMatchChunkLen remaining)
      else
        remaining) := by
  exact dist1ChunkLoopRem.eq_1 (remaining := remaining)

lemma dist1ChunkLoopRem_of_ge3 (remaining : Nat) (h : 3 ≤ remaining) :
    dist1ChunkLoopRem remaining =
      dist1ChunkLoopRem (remaining - chooseFixedMatchChunkLen remaining) := by
  rw [dist1ChunkLoopRem_unfold]
  simp [h]

lemma dist1ChunkLoopRem_of_lt3 (remaining : Nat) (h : ¬ 3 ≤ remaining) :
    dist1ChunkLoopRem remaining = remaining := by
  rw [dist1ChunkLoopRem_unfold]
  simp [h]

lemma dist1ChunkLoopRem_le (remaining : Nat) :
    dist1ChunkLoopRem remaining ≤ remaining := by
  refine Nat.strong_induction_on remaining ?_
  intro remaining ih
  by_cases h : 3 ≤ remaining
  · have hstep : dist1ChunkLoopRem remaining =
      dist1ChunkLoopRem (remaining - chooseFixedMatchChunkLen remaining) := dist1ChunkLoopRem_of_ge3 remaining h
    have hlt : remaining - chooseFixedMatchChunkLen remaining < remaining := by
      exact chooseFixedMatchChunkLen_sub_lt remaining h
    have hih := ih (remaining - chooseFixedMatchChunkLen remaining) hlt
    have hsuble : remaining - chooseFixedMatchChunkLen remaining ≤ remaining := Nat.sub_le _ _
    exact by
      rw [hstep]
      exact le_trans hih hsuble
  · simpa [dist1ChunkLoopRem_of_lt3 remaining h]

lemma dist1ChunkLoopRem_lt3 (remaining : Nat) :
    dist1ChunkLoopRem remaining < 3 := by
  refine Nat.strong_induction_on remaining ?_
  intro remaining ih
  by_cases h : 3 ≤ remaining
  · have hstep : dist1ChunkLoopRem remaining =
      dist1ChunkLoopRem (remaining - chooseFixedMatchChunkLen remaining) := dist1ChunkLoopRem_of_ge3 remaining h
    have hlt : remaining - chooseFixedMatchChunkLen remaining < remaining := by
      exact chooseFixedMatchChunkLen_sub_lt remaining h
    rw [hstep]
    exact ih (remaining - chooseFixedMatchChunkLen remaining) hlt
  · have hlt3 : remaining < 3 := by omega
    simpa [dist1ChunkLoopRem_of_lt3 remaining h] using hlt3

lemma chooseFixedMatchChunkLen_sub_zero_or_ge3 (remaining : Nat) (_hrem : 3 ≤ remaining) :
    remaining - chooseFixedMatchChunkLen remaining = 0 ∨
      3 ≤ remaining - chooseFixedMatchChunkLen remaining := by
  by_cases hgt : remaining > 258
  · by_cases hr1 : (remaining % 258 == 1)
    · right
      have hchunk : chooseFixedMatchChunkLen remaining = 256 := by
        simp [chooseFixedMatchChunkLen, hgt, hr1]
      omega
    · by_cases hr2 : (remaining % 258 == 2)
      · right
        have hchunk : chooseFixedMatchChunkLen remaining = 257 := by
          simp [chooseFixedMatchChunkLen, hgt, hr1, hr2]
        have hne259 : remaining ≠ 259 := by
          intro hEq
          apply hr1
          simp [hEq]
        have hge260 : 260 ≤ remaining := by
          omega
        omega
      · have hchunk : chooseFixedMatchChunkLen remaining = 258 := by
          simp [chooseFixedMatchChunkLen, hgt, hr1, hr2]
        by_cases hsmall : remaining - 258 < 3
        · have honeTwo : remaining - 258 = 1 ∨ remaining - 258 = 2 := by
            omega
          cases honeTwo with
          | inl h1 =>
              exfalso
              have hremEq : remaining = 259 := by omega
              apply hr1
              simp [hremEq]
          | inr h2 =>
              exfalso
              have hremEq : remaining = 260 := by omega
              apply hr2
              simp [hremEq]
        · right
          omega
  · left
    have hle258 : remaining ≤ 258 := Nat.le_of_not_gt hgt
    simp [chooseFixedMatchChunkLen, hgt, hle258]

lemma dist1ChunkLoopRem_eq_zero_of_ge3 (remaining : Nat) (h : 3 ≤ remaining) :
    dist1ChunkLoopRem remaining = 0 := by
  refine Nat.strong_induction_on remaining ?_ h
  intro remaining ih h
  have hstep : dist1ChunkLoopRem remaining =
      dist1ChunkLoopRem (remaining - chooseFixedMatchChunkLen remaining) := by
    exact dist1ChunkLoopRem_of_ge3 remaining h
  rcases chooseFixedMatchChunkLen_sub_zero_or_ge3 remaining h with hzero | hge3
  · rw [hstep, hzero]
    exact dist1ChunkLoopRem_of_lt3 0 (by decide)
  · have hlt : remaining - chooseFixedMatchChunkLen remaining < remaining := by
      exact chooseFixedMatchChunkLen_sub_lt remaining h
    rw [hstep]
    exact ih (remaining - chooseFixedMatchChunkLen remaining) hlt hge3

lemma dist1ChunkLoopOut_eq_pushRepeat
    (out : ByteArray) (remaining : Nat)
    (hout : 0 < out.size) :
    dist1ChunkLoopOut out remaining =
      pushRepeat out (out.get! (out.size - 1)) (remaining - dist1ChunkLoopRem remaining) := by
  revert out hout
  refine Nat.strong_induction_on remaining ?_
  intro remaining ih out hout
  by_cases h : 3 ≤ remaining
  · let chunk := chooseFixedMatchChunkLen remaining
    let rem' := remaining - chunk
    have hchunk : 3 ≤ chunk := (chooseFixedMatchChunkLen_bounds remaining h).1
    have hchunkPos : 0 < chunk := by omega
    have hremEq : dist1ChunkLoopRem remaining = dist1ChunkLoopRem rem' := by
      simpa [chunk, rem'] using (dist1ChunkLoopRem_of_ge3 remaining h)
    have hout' : 0 < (pushRepeat out (out.get! (out.size - 1)) chunk).size := by
      dsimp [chunk]
      exact pushRepeat_pos out (out.get! (out.size - 1)) (chooseFixedMatchChunkLen remaining) hout
    have hlast' :
        (pushRepeat out (out.get! (out.size - 1)) chunk).get!
            ((pushRepeat out (out.get! (out.size - 1)) chunk).size - 1) =
          out.get! (out.size - 1) := by
      have hlast0 : out.get! (out.size - 1) = out.get! (out.size - 1) := rfl
      have hpushLast := pushRepeat_last_get! out (out.get! (out.size - 1)) (out.get! (out.size - 1))
        chunk hout hlast0
      have hchunkNe0 : chunk ≠ 0 := by omega
      simpa [hchunkNe0]
        using hpushLast
    have hih :=
      ih rem' (by simpa [chunk, rem'] using (chooseFixedMatchChunkLen_sub_lt remaining h))
        (pushRepeat out (out.get! (out.size - 1)) chunk) hout'
    have hstep :
        dist1ChunkLoopOut out remaining =
          dist1ChunkLoopOut (pushRepeat out (out.get! (out.size - 1)) chunk) rem' := by
      simpa [chunk, rem'] using (dist1ChunkLoopOut_of_ge3 out remaining h)
    have hih' :
        dist1ChunkLoopOut (pushRepeat out (out.get! (out.size - 1)) chunk) rem' =
          pushRepeat (pushRepeat out (out.get! (out.size - 1)) chunk)
            ((pushRepeat out (out.get! (out.size - 1)) chunk).get!
              ((pushRepeat out (out.get! (out.size - 1)) chunk).size - 1))
            (rem' - dist1ChunkLoopRem rem') := by
      simpa using hih
    calc
      dist1ChunkLoopOut out remaining
          = dist1ChunkLoopOut (pushRepeat out (out.get! (out.size - 1)) chunk) rem' := hstep
      _ = pushRepeat (pushRepeat out (out.get! (out.size - 1)) chunk)
            ((pushRepeat out (out.get! (out.size - 1)) chunk).get!
              ((pushRepeat out (out.get! (out.size - 1)) chunk).size - 1))
            (rem' - dist1ChunkLoopRem rem') := hih'
      _ = pushRepeat (pushRepeat out (out.get! (out.size - 1)) chunk)
            (out.get! (out.size - 1)) (rem' - dist1ChunkLoopRem rem') := by
            exact congrArg
              (fun x =>
                pushRepeat (pushRepeat out (out.get! (out.size - 1)) chunk) x
                  (rem' - dist1ChunkLoopRem rem'))
              (by simpa [pushRepeat_size] using hlast')
      _ = pushRepeat out (out.get! (out.size - 1))
            (chunk + (rem' - dist1ChunkLoopRem rem')) := by
            simpa [chunk, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (pushRepeat_append out (out.get! (out.size - 1)) chunk (rem' - dist1ChunkLoopRem rem'))
      _ = pushRepeat out (out.get! (out.size - 1))
            (remaining - dist1ChunkLoopRem remaining) := by
            have hchunkLe : chunk ≤ remaining := (chooseFixedMatchChunkLen_bounds remaining h).2.2
            have hremLe : dist1ChunkLoopRem rem' ≤ rem' := dist1ChunkLoopRem_le rem'
            have hremEq' : dist1ChunkLoopRem remaining = dist1ChunkLoopRem rem' := hremEq
            have harrith :
                chunk + (rem' - dist1ChunkLoopRem rem') =
                  remaining - dist1ChunkLoopRem remaining := by
              subst rem'
              omega
            simpa [harrith]
  · have hstep : dist1ChunkLoopOut out remaining = out := dist1ChunkLoopOut_of_lt3 out remaining h
    have hrem : dist1ChunkLoopRem remaining = remaining := dist1ChunkLoopRem_of_lt3 remaining h
    simp [hstep, hrem]

def literalRepeatBitsTail (b : UInt8) (n tailBits tailLen : Nat) : Nat × Nat :=
  match n with
  | 0 => (tailBits, tailLen)
  | n + 1 =>
      let rest := literalRepeatBitsTail b n tailBits tailLen
      let tailBits' := rest.1
      let tailLen' := rest.2
      let codeLen := fixedLitLenCode b.toNat
      let bits := reverseBits codeLen.1 codeLen.2
      (bits ||| (tailBits' <<< codeLen.2), codeLen.2 + tailLen')

lemma literalRepeatBitsTail_zero (b : UInt8) (tailBits tailLen : Nat) :
    literalRepeatBitsTail b 0 tailBits tailLen = (tailBits, tailLen) := by
  rfl

lemma literalRepeatBitsTail_succ (b : UInt8) (n tailBits tailLen : Nat) :
    literalRepeatBitsTail b (n + 1) tailBits tailLen =
      let rest := literalRepeatBitsTail b n tailBits tailLen
      let tailBits' := rest.1
      let tailLen' := rest.2
      let codeLen := fixedLitLenCode b.toNat
      let bits := reverseBits codeLen.1 codeLen.2
      (bits ||| (tailBits' <<< codeLen.2), codeLen.2 + tailLen') := by
  rfl

lemma literalRepeatBitsTail_len_ge (b : UInt8) (n tailBits tailLen : Nat) :
    tailLen ≤ (literalRepeatBitsTail b n tailBits tailLen).2 := by
  induction n with
  | zero =>
      simp [literalRepeatBitsTail]
  | succ n ih =>
      rw [literalRepeatBitsTail_succ]
      simp only
      let rest := literalRepeatBitsTail b n tailBits tailLen
      let codeLen := fixedLitLenCode b.toNat
      have hrest : tailLen ≤ rest.2 := by simpa [rest] using ih
      exact le_trans hrest (Nat.le_add_left _ _)

lemma literalRepeatBitsTail_len_ge_two
    (b : UInt8) (n tailBits tailLen : Nat) (htail2 : 2 ≤ tailLen) :
    2 ≤ (literalRepeatBitsTail b n tailBits tailLen).2 := by
  exact le_trans htail2 (literalRepeatBitsTail_len_ge b n tailBits tailLen)

lemma dist1ChunkLoopBitsTail_len_ge (remaining tailBits tailLen : Nat) :
    tailLen ≤ (dist1ChunkLoopBitsTail remaining tailBits tailLen).2 := by
  refine Nat.strong_induction_on remaining ?_
  intro remaining ih
  by_cases h : 3 ≤ remaining
  · let chunk := chooseFixedMatchChunkLen remaining
    let rem' := remaining - chunk
    have hstep := dist1ChunkLoopBitsTail_of_ge3 remaining tailBits tailLen h
    have hlt : rem' < remaining := by
      simpa [chunk, rem'] using (chooseFixedMatchChunkLen_sub_lt remaining h)
    have hih : tailLen ≤ (dist1ChunkLoopBitsTail rem' tailBits tailLen).2 := ih rem' hlt
    rw [hstep]
    simp only
    let rest := dist1ChunkLoopBitsTail rem' tailBits tailLen
    let info := fixedLenMatchInfo chunk
    let sym := info.1
    let extraBits := info.2.1
    let extraLen := info.2.2
    let codeLen := fixedLitLenCode sym
    let distLenTot := 5 + rest.2
    let lenLenTot := extraLen + distLenTot
    let lenTot := codeLen.2 + lenLenTot
    change tailLen ≤ lenTot
    have : rest.2 ≤ lenTot := by
      dsimp [lenTot, lenLenTot, distLenTot]
      omega
    exact le_trans (by simpa [rest] using hih) this
  · simpa [dist1ChunkLoopBitsTail_of_lt3 remaining tailBits tailLen h]

lemma option_do_some {α β : Type} (x : α) (k : α → Option β) :
    (do
      let y ← (some x : Option α)
      k y) = k x := by
  rfl

lemma match_pair_eta {α β γ : Type} (a : α) (b : β) (k : α → β → γ) :
    (match (a, b) with
    | (a, b) => k a b) = k a b := by
  rfl

set_option maxRecDepth 200000 in

def dist1RunBitsTail (b : UInt8) (remaining tailBits tailLen : Nat) : Nat × Nat :=
  let remLit := dist1ChunkLoopRem remaining
  let litTail := literalRepeatBitsTail b remLit tailBits tailLen
  let chunkBits := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (chunkBits.1 <<< codeLen.2)
  let lenTot := codeLen.2 + chunkBits.2
  (bitsTot, lenTot)

def dist1RunSteps (remaining : Nat) : Nat :=
  1 + dist1ChunkLoopSteps remaining + dist1ChunkLoopRem remaining

def dist1RunOut (out : ByteArray) (b : UInt8) (remaining : Nat) : ByteArray :=
  pushRepeat (out.push b) b remaining

lemma dist1RunOut_eq_pushRepeat (out : ByteArray) (b : UInt8) (remaining : Nat) :
    dist1RunOut out b remaining = pushRepeat out b (remaining + 1) := by
  unfold dist1RunOut
  exact pushRepeat_push_eq out b remaining

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

def literalTailWriter (bw : BitWriter) (b : UInt8) (tailBits _tailLen : Nat) : BitWriter :=
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (tailBits <<< codeLen.2)
  BitWriter.writeBits bw bitsTot codeLen.2

def flushReader (bw : BitWriter) (hbit : bw.bitPos < 8) : BitReader :=
  BitWriter.readerAt bw bw.flush (by rfl) hbit

lemma writeBits_or_shift_tail (bw : BitWriter) (bits tailBits len : Nat)
    (hbits : bits < 2 ^ len) :
    BitWriter.writeBits bw (bits ||| (tailBits <<< len)) len = BitWriter.writeBits bw bits len := by
  have hmod : (bits ||| (tailBits <<< len)) % 2 ^ len = bits := by
    calc
      (bits ||| (tailBits <<< len)) % 2 ^ len = bits % 2 ^ len := by
        simpa using (mod_two_pow_or_shift (a := bits) (b := tailBits) (k := len) (len := len) le_rfl)
      _ = bits := Nat.mod_eq_of_lt hbits
  calc
    BitWriter.writeBits bw (bits ||| (tailBits <<< len)) len
        = BitWriter.writeBits bw ((bits ||| (tailBits <<< len)) % 2 ^ len) len := by
            simpa using (writeBits_mod bw (bits ||| (tailBits <<< len)) len)
    _ = BitWriter.writeBits bw bits len := by simp [hmod]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma literalTailWriter_eq_writeFixedLiteralFast
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) :
    literalTailWriter bw b tailBits tailLen = BitWriter.writeFixedLiteralFast bw b := by
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  have hbits : bits < 2 ^ codeLen.2 := by
    simpa [bits] using (reverseBits_lt codeLen.1 codeLen.2)
  have htail :
      literalTailWriter bw b tailBits tailLen = BitWriter.writeBits bw bits codeLen.2 := by
    dsimp [literalTailWriter]
    simpa [codeLen, bits] using
      (writeBits_or_shift_tail (bw := bw) (bits := bits) (tailBits := tailBits) (len := codeLen.2) hbits)
  calc
    literalTailWriter bw b tailBits tailLen = BitWriter.writeBits bw bits codeLen.2 := htail
    _ = BitWriter.writeFixedLiteralFast bw b := by
          simpa [codeLen, bits] using (writeFixedLiteralFast_eq_writeBits (bw := bw) (b := b)).symm

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma writeBits_dist1ChunkLoopBitsTail_three
    (bw : BitWriter) (tailBits tailLen : Nat) :
    BitWriter.writeBits bw (dist1ChunkLoopBitsTail 3 tailBits tailLen).1
      (dist1ChunkLoopBitsTail 3 tailBits tailLen).2 =
      BitWriter.writeBits (BitWriter.writeFixedMatchDist1Fast bw 3) tailBits tailLen := by
  let info := fixedLenMatchInfo 3
  let sym := info.1
  let extraBits := info.2.1
  let extraLen := info.2.2
  let codeLen := fixedLitLenCode sym
  let symBits := reverseBits codeLen.1 codeLen.2
  let distBitsTot := (0 : Nat) ||| (tailBits <<< 5)
  have hsymBits : symBits < 2 ^ codeLen.2 := by
    simpa [symBits] using (reverseBits_lt codeLen.1 codeLen.2)
  have hmod0 : distBitsTot % 2 ^ 5 = 0 := by
    have h := mod_two_pow_or_shift (a := 0) (b := tailBits) (k := 5) (len := 5) (hk := by decide)
    simpa [distBitsTot] using h
  have hprefix0 :
      BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          distBitsTot 5 =
        BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          0 5 := by
    calc
      BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          distBitsTot 5
          =
        BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          (distBitsTot % 2 ^ 5) 5 := by
              simpa using
                (writeBits_mod
                  (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
                  distBitsTot 5)
      _ =
        BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          0 5 := by
            simp [hmod0]
  calc
    BitWriter.writeBits bw (dist1ChunkLoopBitsTail 3 tailBits tailLen).1
        (dist1ChunkLoopBitsTail 3 tailBits tailLen).2
        = BitWriter.writeBits bw (symBits ||| (distBitsTot <<< codeLen.2)) (codeLen.2 + (5 + tailLen)) := by
            simp [dist1ChunkLoopBitsTail_three, info, sym, extraBits, extraLen, codeLen, symBits, distBitsTot,
              fixedLenMatchInfo_three]
    _ = BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) distBitsTot (5 + tailLen) := by
          simpa [Nat.add_assoc] using
            (writeBits_concat bw symBits distBitsTot codeLen.2 (5 + tailLen) hsymBits)
    _ = BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) distBitsTot 5)
          tailBits tailLen := by
            simpa [distBitsTot] using
              (writeBits_dist1Prefix_concat
                (bw := BitWriter.writeBits bw symBits codeLen.2)
                (tailBits := tailBits) (tailLen := tailLen))
    _ = BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) 0 5)
          tailBits tailLen := by
            exact congrArg (fun bw' => BitWriter.writeBits bw' tailBits tailLen) hprefix0
    _ = BitWriter.writeBits (BitWriter.writeFixedMatchDist1Fast bw 3) tailBits tailLen := by
          symm
          simpa [info, sym, extraBits, extraLen, codeLen, symBits,
            fixedLenMatchInfo_three, writeBits_zero] using
            congrArg (fun bw' => BitWriter.writeBits bw' tailBits tailLen)
              (writeFixedMatchDist1Fast_eq_writeBits_chain (bw := bw) (matchLen := 3) (hlen := by decide))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma writeBits_dist1RunBitsTail_three
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) :
    BitWriter.writeBits bw (dist1RunBitsTail b 3 tailBits tailLen).1
      (dist1RunBitsTail b 3 tailBits tailLen).2 =
      BitWriter.writeBits ((BitWriter.writeFixedLiteralFast bw b).writeFixedMatchDist1Fast 3) tailBits tailLen := by
  let chunkBits := dist1ChunkLoopBitsTail 3 tailBits tailLen
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  have hbits : bits < 2 ^ codeLen.2 := by
    simpa [bits] using (reverseBits_lt codeLen.1 codeLen.2)
  calc
    BitWriter.writeBits bw (dist1RunBitsTail b 3 tailBits tailLen).1
        (dist1RunBitsTail b 3 tailBits tailLen).2
        = BitWriter.writeBits bw (bits ||| (chunkBits.1 <<< codeLen.2)) (codeLen.2 + chunkBits.2) := by
            simp [dist1RunBitsTail_three, chunkBits, codeLen, bits]
    _ = BitWriter.writeBits (BitWriter.writeBits bw bits codeLen.2) chunkBits.1 chunkBits.2 := by
          simpa [chunkBits, Nat.add_assoc] using
            (writeBits_concat bw bits chunkBits.1 codeLen.2 chunkBits.2 hbits)
    _ = BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) chunkBits.1 chunkBits.2 := by
          simpa [codeLen, bits] using congrArg (fun bw' => BitWriter.writeBits bw' chunkBits.1 chunkBits.2)
            (writeFixedLiteralFast_eq_writeBits (bw := bw) (b := b))
    _ = BitWriter.writeBits ((BitWriter.writeFixedLiteralFast bw b).writeFixedMatchDist1Fast 3) tailBits tailLen := by
          simpa [chunkBits] using
            (writeBits_dist1ChunkLoopBitsTail_three
              (bw := BitWriter.writeFixedLiteralFast bw b)
              (tailBits := tailBits) (tailLen := tailLen))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma writeBits_literalRepeatBitsTail_one
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) :
    BitWriter.writeBits bw (literalRepeatBitsTail b 1 tailBits tailLen).1
      (literalRepeatBitsTail b 1 tailBits tailLen).2 =
      BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen := by
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  have hbits : bits < 2 ^ codeLen.2 := by
    simpa [bits] using (reverseBits_lt codeLen.1 codeLen.2)
  calc
    BitWriter.writeBits bw (literalRepeatBitsTail b 1 tailBits tailLen).1
        (literalRepeatBitsTail b 1 tailBits tailLen).2
        = BitWriter.writeBits bw (bits ||| (tailBits <<< codeLen.2)) (codeLen.2 + tailLen) := by
            simp [literalRepeatBitsTail_succ, literalRepeatBitsTail_zero, codeLen, bits]
    _ = BitWriter.writeBits (BitWriter.writeBits bw bits codeLen.2) tailBits tailLen := by
          simpa [Nat.add_assoc] using (writeBits_concat bw bits tailBits codeLen.2 tailLen hbits)
    _ = BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen := by
          simpa [codeLen, bits] using congrArg (fun bw' => BitWriter.writeBits bw' tailBits tailLen)
            (writeFixedLiteralFast_eq_writeBits (bw := bw) (b := b))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma writeBits_literalRepeatBitsTail_one_helper
    (bw : BitWriter) (b : UInt8) (tailBits tailLen : Nat) :
    BitWriter.writeBits bw (literalRepeatBitsTail b 1 tailBits tailLen).1
      (literalRepeatBitsTail b 1 tailBits tailLen).2 =
      BitWriter.writeBits (literalTailWriter bw b tailBits tailLen) tailBits tailLen := by
  calc
    BitWriter.writeBits bw (literalRepeatBitsTail b 1 tailBits tailLen).1
        (literalRepeatBitsTail b 1 tailBits tailLen).2
        = BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) tailBits tailLen := by
            exact writeBits_literalRepeatBitsTail_one (bw := bw) (b := b)
              (tailBits := tailBits) (tailLen := tailLen)
    _ = BitWriter.writeBits (literalTailWriter bw b tailBits tailLen) tailBits tailLen := by
          simp [literalTailWriter_eq_writeFixedLiteralFast]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma writeBits_literalRepeatBitsTail
    (bw : BitWriter) (b : UInt8) (n tailBits tailLen : Nat) :
    BitWriter.writeBits bw (literalRepeatBitsTail b n tailBits tailLen).1
      (literalRepeatBitsTail b n tailBits tailLen).2 =
      BitWriter.writeBits (bw.writeFixedLiteralRepeatFast b n) tailBits tailLen := by
  induction n generalizing bw with
  | zero =>
      simp [BitWriter.writeFixedLiteralRepeatFast, literalRepeatBitsTail_zero]
  | succ n ih =>
      let rest := literalRepeatBitsTail b n tailBits tailLen
      calc
        BitWriter.writeBits bw (literalRepeatBitsTail b (n + 1) tailBits tailLen).1
            (literalRepeatBitsTail b (n + 1) tailBits tailLen).2
            =
          BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) rest.1 rest.2 := by
              simpa [literalRepeatBitsTail_succ, rest] using
                (writeBits_literalRepeatBitsTail_one
                  (bw := bw) (b := b) (tailBits := rest.1) (tailLen := rest.2))
        _ =
          BitWriter.writeBits
            ((BitWriter.writeFixedLiteralFast bw b).writeFixedLiteralRepeatFast b n)
            tailBits tailLen := by
              simpa [rest] using ih (bw := BitWriter.writeFixedLiteralFast bw b)
        _ =
          BitWriter.writeBits (bw.writeFixedLiteralRepeatFast b (n + 1)) tailBits tailLen := by
              rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma writeBits_dist1ChunkStep
    (bw : BitWriter) (chunk tailBits tailLen : Nat)
    (hlen : 3 ≤ chunk ∧ chunk ≤ 258) :
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
    BitWriter.writeBits bw bitsTot lenTot =
      BitWriter.writeBits (BitWriter.writeFixedMatchDist1Fast bw chunk) tailBits tailLen := by
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
  have hsymBits : symBits < 2 ^ codeLen.2 := by
    simpa [symBits] using (reverseBits_lt codeLen.1 codeLen.2)
  have hmod0 : distBitsTot % 2 ^ 5 = 0 := by
    have h := mod_two_pow_or_shift (a := 0) (b := tailBits) (k := 5) (len := 5) (hk := by decide)
    simpa [distBitsTot] using h
  have hprefix0 :
      BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          distBitsTot 5 =
        BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          0 5 := by
    calc
      BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          distBitsTot 5
          =
        BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          (distBitsTot % 2 ^ 5) 5 := by
              simpa using
                (writeBits_mod
                  (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
                  distBitsTot 5)
      _ =
        BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          0 5 := by
            simp [hmod0]
  calc
    BitWriter.writeBits bw bitsTot lenTot
        = BitWriter.writeBits bw (symBits ||| (lenBitsTot <<< codeLen.2)) (codeLen.2 + (extraLen + (5 + tailLen))) := by
            simp [bitsTot, lenTot, lenLenTot, distLenTot]
    _ = BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) lenBitsTot (extraLen + (5 + tailLen)) := by
          simpa [Nat.add_assoc] using
            (writeBits_concat bw symBits lenBitsTot codeLen.2 (extraLen + (5 + tailLen)) hsymBits)
    _ = BitWriter.writeBits
          (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
          distBitsTot (5 + tailLen) := by
            have hbitsLt : extraBits < 2 ^ extraLen := by
              have hinfo := fixedLenMatchInfo_spec_get! chunk hlen.1 hlen.2
              simpa [info, sym, extraBits, extraLen] using hinfo.2.2.2.2
            simpa [lenBitsTot, Nat.add_assoc] using
              (writeBits_concat
                (BitWriter.writeBits bw symBits codeLen.2) extraBits distBitsTot extraLen (5 + tailLen) hbitsLt)
    _ = BitWriter.writeBits
          (BitWriter.writeBits
            (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
            distBitsTot 5)
          tailBits tailLen := by
            simpa [distBitsTot] using
              (writeBits_dist1Prefix_concat
                (bw := BitWriter.writeBits
                  (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
                (tailBits := tailBits) (tailLen := tailLen))
    _ = BitWriter.writeBits
          (BitWriter.writeBits
            (BitWriter.writeBits (BitWriter.writeBits bw symBits codeLen.2) extraBits extraLen)
            0 5)
          tailBits tailLen := by
            exact congrArg (fun bw' => BitWriter.writeBits bw' tailBits tailLen) hprefix0
    _ = BitWriter.writeBits (BitWriter.writeFixedMatchDist1Fast bw chunk) tailBits tailLen := by
          symm
          simpa [info, sym, extraBits, extraLen, codeLen, symBits, writeBits_zero] using
            congrArg (fun bw' => BitWriter.writeBits bw' tailBits tailLen)
              (writeFixedMatchDist1Fast_eq_writeBits_chain (bw := bw) (matchLen := chunk) (hlen := hlen))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma writeBits_dist1ChunkLoopBitsTail
    (bw : BitWriter) (remaining tailBits tailLen : Nat) :
    BitWriter.writeBits bw (dist1ChunkLoopBitsTail remaining tailBits tailLen).1
      (dist1ChunkLoopBitsTail remaining tailBits tailLen).2 =
      BitWriter.writeBits (bw.writeFixedMatchDist1ChunksFast remaining) tailBits tailLen := by
  have hk :
      ∀ remaining bw tailBits tailLen,
        BitWriter.writeBits bw (dist1ChunkLoopBitsTail remaining tailBits tailLen).1
          (dist1ChunkLoopBitsTail remaining tailBits tailLen).2 =
          BitWriter.writeBits (bw.writeFixedMatchDist1ChunksFast remaining) tailBits tailLen := by
    intro remaining
    refine Nat.strong_induction_on remaining ?_
    intro remaining ih bw tailBits tailLen
    by_cases h : 3 ≤ remaining
    · let chunk := chooseFixedMatchChunkLen remaining
      let rem := remaining - chunk
      let rest := dist1ChunkLoopBitsTail rem tailBits tailLen
      have hlt : rem < remaining := by
        simpa [chunk, rem] using (chooseFixedMatchChunkLen_sub_lt remaining h)
      have hchunk : 3 ≤ chunk ∧ chunk ≤ 258 := by
        have hbounds := chooseFixedMatchChunkLen_bounds remaining h
        exact ⟨by simpa [chunk] using hbounds.1, by simpa [chunk] using hbounds.2.1⟩
      calc
        BitWriter.writeBits bw (dist1ChunkLoopBitsTail remaining tailBits tailLen).1
            (dist1ChunkLoopBitsTail remaining tailBits tailLen).2
            =
          BitWriter.writeBits (BitWriter.writeFixedMatchDist1Fast bw chunk) rest.1 rest.2 := by
              rw [dist1ChunkLoopBitsTail_of_ge3 remaining tailBits tailLen h]
              simpa [chunk, rem, rest] using
                (writeBits_dist1ChunkStep
                  (bw := bw) (chunk := chunk) (tailBits := rest.1) (tailLen := rest.2) hchunk)
        _ =
          BitWriter.writeBits
            ((BitWriter.writeFixedMatchDist1Fast bw chunk).writeFixedMatchDist1ChunksFast rem)
            tailBits tailLen := by
              simpa [rest] using
                (ih rem hlt (BitWriter.writeFixedMatchDist1Fast bw chunk) tailBits tailLen)
        _ = BitWriter.writeBits (bw.writeFixedMatchDist1ChunksFast remaining) tailBits tailLen := by
              have hdef :
                  bw.writeFixedMatchDist1ChunksFast remaining =
                    (bw.writeFixedMatchDist1Fast chunk).writeFixedMatchDist1ChunksFast rem := by
                rw [BitWriter.writeFixedMatchDist1ChunksFast.eq_1]
                simp [h, chunk, rem]
              rw [hdef]
    · simp [dist1ChunkLoopBitsTail_of_lt3 remaining tailBits tailLen h, BitWriter.writeFixedMatchDist1ChunksFast, h]
  exact hk remaining bw tailBits tailLen

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
lemma writeBits_dist1RunBitsTail
    (bw : BitWriter) (b : UInt8) (remaining tailBits tailLen : Nat)
    (hrem : 3 ≤ remaining) :
    BitWriter.writeBits bw (dist1RunBitsTail b remaining tailBits tailLen).1
      (dist1RunBitsTail b remaining tailBits tailLen).2 =
      BitWriter.writeBits ((BitWriter.writeFixedLiteralFast bw b).writeFixedMatchDist1ChunksFast remaining)
        tailBits tailLen := by
  let remLit := dist1ChunkLoopRem remaining
  let chunkBits := dist1ChunkLoopBitsTail remaining tailBits tailLen
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  have hremLit0 : remLit = 0 := by
    dsimp [remLit]
    exact dist1ChunkLoopRem_eq_zero_of_ge3 remaining hrem
  have hbits : bits < 2 ^ codeLen.2 := by
    simpa [bits] using (reverseBits_lt codeLen.1 codeLen.2)
  calc
    BitWriter.writeBits bw (dist1RunBitsTail b remaining tailBits tailLen).1
        (dist1RunBitsTail b remaining tailBits tailLen).2
        = BitWriter.writeBits bw (bits ||| (chunkBits.1 <<< codeLen.2)) (codeLen.2 + chunkBits.2) := by
            simp [dist1RunBitsTail, remLit, hremLit0, literalRepeatBitsTail_zero, chunkBits, codeLen, bits]
    _ = BitWriter.writeBits (BitWriter.writeBits bw bits codeLen.2) chunkBits.1 chunkBits.2 := by
          simpa [chunkBits, Nat.add_assoc] using
            (writeBits_concat bw bits chunkBits.1 codeLen.2 chunkBits.2 hbits)
    _ = BitWriter.writeBits (BitWriter.writeFixedLiteralFast bw b) chunkBits.1 chunkBits.2 := by
          simpa [codeLen, bits] using
            congrArg (fun bw' => BitWriter.writeBits bw' chunkBits.1 chunkBits.2)
              (writeFixedLiteralFast_eq_writeBits (bw := bw) (b := b))
    _ =
      BitWriter.writeBits ((BitWriter.writeFixedLiteralFast bw b).writeFixedMatchDist1ChunksFast remaining)
        tailBits tailLen := by
          simpa [chunkBits] using
            (writeBits_dist1ChunkLoopBitsTail
              (bw := BitWriter.writeFixedLiteralFast bw b)
              (remaining := remaining) (tailBits := tailBits) (tailLen := tailLen))

end Png
end Bitmaps
