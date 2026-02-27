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
      rw [hidxSucc]
      cases n <;> simpa using hrec

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
  simpa [Std.Range.forIn_eq_forIn_range'] using
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

def literalTailWriter (bw : BitWriter) (b : UInt8) (tailBits _tailLen : Nat) : BitWriter :=
  let codeLen := fixedLitLenCode b.toNat
  let bits := reverseBits codeLen.1 codeLen.2
  let bitsTot := bits ||| (tailBits <<< codeLen.2)
  BitWriter.writeBits bw bitsTot codeLen.2

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

def eobNoTailWriter (bw : BitWriter) : BitWriter :=
  let sym : Nat := 256
  let codeLen := fixedLitLenCode sym
  let bits := reverseBits codeLen.1 codeLen.2
  BitWriter.writeBits bw bits codeLen.2

def eobNoTailStartReader (bw : BitWriter) (hbit : bw.bitPos < 8) : BitReader :=
  let bwAll := eobNoTailWriter bw
  BitWriter.readerAt bw bwAll.flush
    (by
      have symEq : (256 : Nat) = 256 := rfl
      simpa [eobNoTailWriter, symEq] using
        (flush_size_writeBits_le (bw := bw)
          (bits := reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
          (len := (fixedLitLenCode 256).2)))
    hbit

def eobNoTailAfterReader (bw : BitWriter) (hbit : bw.bitPos < 8) : BitReader :=
  let bwAll := eobNoTailWriter bw
  BitWriter.readerAt bwAll bwAll.flush
    (by rfl)
    (by
      have symEq : (256 : Nat) = 256 := rfl
      simpa [eobNoTailWriter, symEq] using
        (bitPos_lt_8_writeBits (bw := bw)
          (bits := reverseBits (fixedLitLenCode 256).1 (fixedLitLenCode 256).2)
          (len := (fixedLitLenCode 256).2) hbit))

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

def sameByteRunEnd (data : Array UInt8) (b : UInt8) (j : Nat) : Nat :=
  if h : j < data.size then
    if data[j]'h = b then
      sameByteRunEnd data b (j + 1)
    else
      j
  else
    j
termination_by data.size - j
decreasing_by
  have hlt : j < data.size := h
  exact Nat.sub_lt_sub_left (k := j) (m := data.size) (n := j + 1) hlt (Nat.lt_succ_self j)

lemma sameByteRunEnd_ge (data : Array UInt8) (b : UInt8) (j : Nat) :
    j ≤ sameByteRunEnd data b j := by
  rw [sameByteRunEnd.eq_def]
  by_cases h : j < data.size
  · by_cases heq : data[j]'h = b
    · have hrec := sameByteRunEnd_ge data b (j + 1)
      simp [h, heq]
      omega
    · simp [h, heq]
  · simp [h]

lemma sameByteRunEnd_le_size (data : Array UInt8) (b : UInt8) (j : Nat)
    (hj : j ≤ data.size) :
    sameByteRunEnd data b j ≤ data.size := by
  rw [sameByteRunEnd.eq_def]
  by_cases h : j < data.size
  · by_cases heq : data[j]'h = b
    · simp [h, heq]
      exact sameByteRunEnd_le_size data b (j + 1) (Nat.succ_le_of_lt h)
    · simp [h, heq]
      omega
  · simp [h]
    exact hj

lemma sameByteRunEnd_gt_prev
    (data : Array UInt8) (i : Nat) (h : i < data.size) :
    i < sameByteRunEnd data data[i] (i + 1) := by
  have hge : i + 1 ≤ sameByteRunEnd data data[i] (i + 1) :=
    sameByteRunEnd_ge data data[i] (i + 1)
  omega

lemma sameByteRunEnd_stop_ne (data : Array UInt8) (b : UInt8) (j : Nat)
    (hend : sameByteRunEnd data b j < data.size) :
    data[sameByteRunEnd data b j]'hend ≠ b := by
  rw [sameByteRunEnd.eq_def] at hend
  by_cases h : j < data.size
  · by_cases heq : data[j]'h = b
    · simp [h, heq] at hend
      have hs : sameByteRunEnd data b j = sameByteRunEnd data b (j + 1) := by
        rw [sameByteRunEnd.eq_def]
        simp [h, heq]
      simpa [hs] using (sameByteRunEnd_stop_ne data b (j + 1) hend)
    · have hs : sameByteRunEnd data b j = j := by
        rw [sameByteRunEnd.eq_def]
        simp [h, heq]
      simpa [hs] using heq
  · simp [sameByteRunEnd.eq_def, h] at hend

lemma byteArrayFromArray_sameByteRunEnd_pushRepeat
    (data : Array UInt8) (b : UInt8) (i : Nat) (out : ByteArray) :
    byteArrayFromArray data i out =
      byteArrayFromArray data (sameByteRunEnd data b i)
        (pushRepeat out b (sameByteRunEnd data b i - i)) := by
  classical
  by_cases h : i < data.size
  · by_cases heq : data[i]'h = b
    · have hrec :=
        byteArrayFromArray_sameByteRunEnd_pushRepeat data b (i + 1) (out.push b)
      have hs :
          sameByteRunEnd data b i = sameByteRunEnd data b (i + 1) := by
        rw [sameByteRunEnd.eq_def]
        simp [h, heq]
      have hgt : i < sameByteRunEnd data b (i + 1) := by
        have hge : i + 1 ≤ sameByteRunEnd data b (i + 1) := sameByteRunEnd_ge data b (i + 1)
        omega
      have hdiff :
          sameByteRunEnd data b (i + 1) - i =
            (sameByteRunEnd data b (i + 1) - (i + 1)) + 1 := by
        omega
      have hpush :
          pushRepeat out b (sameByteRunEnd data b (i + 1) - i) =
            pushRepeat (out.push b) b (sameByteRunEnd data b (i + 1) - (i + 1)) := by
        have htmp := pushRepeat_push_eq out b (sameByteRunEnd data b (i + 1) - (i + 1))
        -- rewrite both sides to the canonical `pushRepeat out b (_ + 1)` form
        calc
          pushRepeat out b (sameByteRunEnd data b (i + 1) - i)
              = pushRepeat out b ((sameByteRunEnd data b (i + 1) - (i + 1)) + 1) := by
                  simp [hdiff]
          _ = pushRepeat (out.push b) b (sameByteRunEnd data b (i + 1) - (i + 1)) := by
                  simpa using htmp.symm
      rw [byteArrayFromArray_unfold]
      have hdatai : data[i] = b := by simpa using heq
      simp [h, hdatai]
      calc
        byteArrayFromArray data (i + 1) (out.push b)
            = byteArrayFromArray data (sameByteRunEnd data b (i + 1))
                (pushRepeat (out.push b) b (sameByteRunEnd data b (i + 1) - (i + 1))) := hrec
        _ = byteArrayFromArray data (sameByteRunEnd data b (i + 1))
                (pushRepeat out b (sameByteRunEnd data b (i + 1) - i)) := by
              simp [hpush]
        _ = byteArrayFromArray data (sameByteRunEnd data b i)
                (pushRepeat out b (sameByteRunEnd data b i - i)) := by
              rw [← hs]
    · have hs : sameByteRunEnd data b i = i := by
        rw [sameByteRunEnd.eq_def]
        simp [h, heq]
      simpa [hs]
  · have hs : sameByteRunEnd data b i = i := by
      rw [sameByteRunEnd.eq_def]
      simp [h]
    have hba : byteArrayFromArray data i out = out := by
      rw [byteArrayFromArray_unfold]
      simp [h]
    calc
      byteArrayFromArray data i out = out := hba
      _ = byteArrayFromArray data (sameByteRunEnd data b i)
            (pushRepeat out b (sameByteRunEnd data b i - i)) := by
            simpa [hs] using hba.symm

def fixedRunScanBitsEob (data : Array UInt8) (i : Nat) : Nat × Nat :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEnd data b (i + 1)
    let runLen := j - i
    let tail := fixedRunScanBitsEob data j
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
  let j := sameByteRunEnd data data[i] (i + 1)
  have hgt : i < j := by
    exact sameByteRunEnd_gt_prev data i hlt
  have hle : j ≤ data.size := by
    exact sameByteRunEnd_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  omega

def fixedRunScanStepsEob (data : Array UInt8) (i : Nat) : Nat :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEnd data b (i + 1)
    let runLen := j - i
    let tail := fixedRunScanStepsEob data j
    if 4 ≤ runLen then
      dist1RunSteps (runLen - 1) + tail
    else
      runLen + tail
  else
    1
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  let j := sameByteRunEnd data data[i] (i + 1)
  have hgt : i < j := by
    exact sameByteRunEnd_gt_prev data i hlt
  have hle : j ≤ data.size := by
    exact sameByteRunEnd_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  omega

def fixedRunScanOut (data : Array UInt8) (i : Nat) (out : ByteArray) : ByteArray :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEnd data b (i + 1)
    let runLen := j - i
    let out' :=
      if 4 ≤ runLen then
        dist1RunOut out b (runLen - 1)
      else
        pushRepeat out b runLen
    fixedRunScanOut data j out'
  else
    out
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  let j := sameByteRunEnd data data[i] (i + 1)
  have hgt : i < j := by
    exact sameByteRunEnd_gt_prev data i hlt
  have hle : j ≤ data.size := by
    exact sameByteRunEnd_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  omega

lemma fixedRunScanBitsEob_unfold (data : Array UInt8) (i : Nat) :
    fixedRunScanBitsEob data i =
      (if h : i < data.size then
        let b := data[i]
        let j := sameByteRunEnd data b (i + 1)
        let runLen := j - i
        let tail := fixedRunScanBitsEob data j
        if 4 ≤ runLen then
          dist1RunBitsTail b (runLen - 1) tail.1 tail.2
        else
          literalRepeatBitsTail b runLen tail.1 tail.2
      else
        let eob := fixedLitLenCode 256
        (reverseBits eob.1 eob.2, eob.2)) := by
  exact fixedRunScanBitsEob.eq_1 (data := data) (i := i)

lemma fixedRunScanStepsEob_unfold (data : Array UInt8) (i : Nat) :
    fixedRunScanStepsEob data i =
      (if h : i < data.size then
        let b := data[i]
        let j := sameByteRunEnd data b (i + 1)
        let runLen := j - i
        let tail := fixedRunScanStepsEob data j
        if 4 ≤ runLen then
          dist1RunSteps (runLen - 1) + tail
        else
          runLen + tail
      else
        1) := by
  exact fixedRunScanStepsEob.eq_1 (data := data) (i := i)

lemma fixedRunScanOut_unfold (data : Array UInt8) (i : Nat) (out : ByteArray) :
    fixedRunScanOut data i out =
      (if h : i < data.size then
        let b := data[i]
        let j := sameByteRunEnd data b (i + 1)
        let runLen := j - i
        let out' :=
          if 4 ≤ runLen then
            dist1RunOut out b (runLen - 1)
          else
            pushRepeat out b runLen
        fixedRunScanOut data j out'
      else
        out) := by
  exact fixedRunScanOut.eq_1 (data := data) (i := i) (out := out)

lemma fixedRunScanOut_eq_byteArrayFromArray (data : Array UInt8) (i : Nat) (out : ByteArray) :
    fixedRunScanOut data i out = byteArrayFromArray data i out := by
  classical
  rw [fixedRunScanOut.eq_1]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    let j := sameByteRunEnd data b (i + 1)
    let runLen := j - i
    have hnext : sameByteRunEnd data data[i] (i + 1) = j := by
      simpa [b, j]
    have hrun : sameByteRunEnd data data[i] (i + 1) - i = runLen := by
      simpa [b, j, runLen]
    have hscan0 : sameByteRunEnd data b i = j := by
      rw [sameByteRunEnd.eq_def]
      simp [hlt, b, hnext]
    have hbaRun :
        byteArrayFromArray data i out =
          byteArrayFromArray data j (pushRepeat out b runLen) := by
      have htmp := byteArrayFromArray_sameByteRunEnd_pushRepeat data b i out
      simpa [j, runLen, hscan0] using htmp
    by_cases h4 : 4 ≤ runLen
    · have hih :
          fixedRunScanOut data j (dist1RunOut out b (runLen - 1)) =
            byteArrayFromArray data j (dist1RunOut out b (runLen - 1)) := by
          exact fixedRunScanOut_eq_byteArrayFromArray data j (dist1RunOut out b (runLen - 1))
      have hgt : i < j := by
        dsimp [j, b]
        exact sameByteRunEnd_gt_prev data i hlt
      have hrunPos : 0 < runLen := by
        dsimp [runLen]
        omega
      have haccEq : dist1RunOut out b (runLen - 1) = pushRepeat out b runLen := by
        have htmp := dist1RunOut_eq_pushRepeat out b (runLen - 1)
        have harrith : (runLen - 1) + 1 = runLen := by
          omega
        simpa [harrith] using htmp
      have hmid :
          fixedRunScanOut data j (dist1RunOut out b (runLen - 1)) =
            byteArrayFromArray data i out := by
        refine hih.trans ?_
        calc
          byteArrayFromArray data j (dist1RunOut out b (runLen - 1))
              = byteArrayFromArray data j (pushRepeat out b runLen) := by
                  simp [haccEq]
          _ = byteArrayFromArray data i out := hbaRun.symm
      simpa [b, j, runLen, hnext, hrun, h4] using hmid
    · have hih :
          fixedRunScanOut data j (pushRepeat out b runLen) =
            byteArrayFromArray data j (pushRepeat out b runLen) := by
          exact fixedRunScanOut_eq_byteArrayFromArray data j (pushRepeat out b runLen)
      simpa [b, j, runLen, hnext, hrun, h4] using hih.trans hbaRun.symm
  · rw [byteArrayFromArray_unfold]
    simp [hlt]
termination_by data.size - i
decreasing_by
  all_goals
    have hlt' : i < data.size := hlt
    have hgt : i < sameByteRunEnd data data[i] (i + 1) := by
      exact sameByteRunEnd_gt_prev data i hlt'
    have hle : sameByteRunEnd data data[i] (i + 1) ≤ data.size := by
      exact sameByteRunEnd_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt')
    omega

def quadTailEqb (data : Array UInt8) (i : Nat) (b : UInt8) (h3 : i + 3 < data.size) : Bool :=
  let b1 := data[i + 1]'(by omega)
  let b2 := data[i + 2]'(by omega)
  let b3 := data[i + 3]'h3
  (b1 == b) && (b2 == b) && (b3 == b)

lemma quadTailEqb_eq_true
    (data : Array UInt8) (i : Nat) (b : UInt8) (h3 : i + 3 < data.size) :
    quadTailEqb data i b h3 = true ↔
      data[i + 1]'(by omega) = b ∧
      data[i + 2]'(by omega) = b ∧
      data[i + 3]'h3 = b := by
  unfold quadTailEqb
  simp [Bool.and_eq_true, and_assoc]

def fixedQuadBitsEob (data : Array UInt8) (i : Nat) : Nat × Nat :=
  if h : i < data.size then
    let b := data[i]
    if h3 : i + 3 < data.size then
      if quadTailEqb data i b h3 then
        let tail := fixedQuadBitsEob data (i + 4)
        dist1RunBitsTail b 3 tail.1 tail.2
      else
        let tail := fixedQuadBitsEob data (i + 1)
        literalRepeatBitsTail b 1 tail.1 tail.2
    else
      let tail := fixedQuadBitsEob data (i + 1)
      literalRepeatBitsTail b 1 tail.1 tail.2
  else
    let eob := fixedLitLenCode 256
    (reverseBits eob.1 eob.2, eob.2)
termination_by data.size - i
decreasing_by
  · have hle : data.size - (i + 4) < data.size - i := by
      omega
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle

def fixedQuadStepsEob (data : Array UInt8) (i : Nat) : Nat :=
  if h : i < data.size then
    let b := data[i]
    if h3 : i + 3 < data.size then
      if quadTailEqb data i b h3 then
        dist1RunSteps 3 + fixedQuadStepsEob data (i + 4)
      else
        1 + fixedQuadStepsEob data (i + 1)
    else
      1 + fixedQuadStepsEob data (i + 1)
  else
    1
termination_by data.size - i
decreasing_by
  · have hle : data.size - (i + 4) < data.size - i := by
      omega
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle

def fixedQuadOut (data : Array UInt8) (i : Nat) (out : ByteArray) : ByteArray :=
  if h : i < data.size then
    let b := data[i]
    if h3 : i + 3 < data.size then
      if quadTailEqb data i b h3 then
        fixedQuadOut data (i + 4) (dist1RunOut out b 3)
      else
        fixedQuadOut data (i + 1) (out.push b)
    else
      fixedQuadOut data (i + 1) (out.push b)
  else
    out
termination_by data.size - i
decreasing_by
  · have hle : data.size - (i + 4) < data.size - i := by
      omega
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle

lemma fixedQuadBitsEob_unfold (data : Array UInt8) (i : Nat) :
    fixedQuadBitsEob data i =
      (if h : i < data.size then
        let b := data[i]
        if h3 : i + 3 < data.size then
          if quadTailEqb data i b h3 then
            let tail := fixedQuadBitsEob data (i + 4)
            dist1RunBitsTail b 3 tail.1 tail.2
          else
            let tail := fixedQuadBitsEob data (i + 1)
            literalRepeatBitsTail b 1 tail.1 tail.2
        else
          let tail := fixedQuadBitsEob data (i + 1)
          literalRepeatBitsTail b 1 tail.1 tail.2
      else
        let eob := fixedLitLenCode 256
        (reverseBits eob.1 eob.2, eob.2)) := by
  exact fixedQuadBitsEob.eq_1 (data := data) (i := i)

lemma fixedQuadStepsEob_unfold (data : Array UInt8) (i : Nat) :
    fixedQuadStepsEob data i =
      (if h : i < data.size then
        let b := data[i]
        if h3 : i + 3 < data.size then
          if quadTailEqb data i b h3 then
            dist1RunSteps 3 + fixedQuadStepsEob data (i + 4)
          else
            1 + fixedQuadStepsEob data (i + 1)
        else
          1 + fixedQuadStepsEob data (i + 1)
      else
        1) := by
  exact fixedQuadStepsEob.eq_1 (data := data) (i := i)

lemma fixedQuadOut_unfold (data : Array UInt8) (i : Nat) (out : ByteArray) :
    fixedQuadOut data i out =
      (if h : i < data.size then
        let b := data[i]
        if h3 : i + 3 < data.size then
          if quadTailEqb data i b h3 then
            fixedQuadOut data (i + 4) (dist1RunOut out b 3)
          else
            fixedQuadOut data (i + 1) (out.push b)
        else
          fixedQuadOut data (i + 1) (out.push b)
      else
        out) := by
  exact fixedQuadOut.eq_1 (data := data) (i := i) (out := out)

lemma dist1RunBitsTail_len_ge (b : UInt8) (remaining tailBits tailLen : Nat) :
    tailLen ≤ (dist1RunBitsTail b remaining tailBits tailLen).2 := by
  unfold dist1RunBitsTail
  let remLit := dist1ChunkLoopRem remaining
  let litTail := literalRepeatBitsTail b remLit tailBits tailLen
  let chunkBits := dist1ChunkLoopBitsTail remaining litTail.1 litTail.2
  let codeLen := fixedLitLenCode b.toNat
  have hlit : tailLen ≤ litTail.2 := by
    dsimp [litTail]
    exact literalRepeatBitsTail_len_ge b remLit tailBits tailLen
  have hchunk : litTail.2 ≤ chunkBits.2 := by
    dsimp [chunkBits]
    exact dist1ChunkLoopBitsTail_len_ge remaining litTail.1 litTail.2
  have hcode : chunkBits.2 ≤ codeLen.2 + chunkBits.2 := Nat.le_add_left _ _
  exact le_trans hlit (le_trans hchunk hcode)

lemma dist1RunBitsTail_len_ge_two
    (b : UInt8) (remaining tailBits tailLen : Nat) (htail2 : 2 ≤ tailLen) :
    2 ≤ (dist1RunBitsTail b remaining tailBits tailLen).2 := by
  exact le_trans htail2 (dist1RunBitsTail_len_ge b remaining tailBits tailLen)

lemma fixedRunScanBitsEob_len_ge_two (data : Array UInt8) (i : Nat) :
    2 ≤ (fixedRunScanBitsEob data i).2 := by
  classical
  rw [fixedRunScanBitsEob.eq_1]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    let j := sameByteRunEnd data b (i + 1)
    let runLen := j - i
    have htail : 2 ≤ (fixedRunScanBitsEob data j).2 := by
      exact fixedRunScanBitsEob_len_ge_two data j
    by_cases h4 : 4 ≤ runLen
    · simpa [b, j, runLen, h4] using
        (dist1RunBitsTail_len_ge_two b (runLen - 1) (fixedRunScanBitsEob data j).1
          (fixedRunScanBitsEob data j).2 htail)
    · simpa [b, j, runLen, h4] using
        (literalRepeatBitsTail_len_ge_two b runLen (fixedRunScanBitsEob data j).1
          (fixedRunScanBitsEob data j).2 htail)
  · simp [hlt, fixedLitLenCode]
termination_by data.size - i
decreasing_by
  have hlt' : i < data.size := hlt
  have hgt : i < sameByteRunEnd data data[i] (i + 1) := by
    exact sameByteRunEnd_gt_prev data i hlt'
  have hle : sameByteRunEnd data data[i] (i + 1) ≤ data.size := by
    exact sameByteRunEnd_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt')
  omega

lemma fixedQuadBitsEob_len_ge_two (data : Array UInt8) (i : Nat) :
    2 ≤ (fixedQuadBitsEob data i).2 := by
  classical
  rw [fixedQuadBitsEob_unfold]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    by_cases h3 : i + 3 < data.size
    · dsimp [b]
      by_cases hq : quadTailEqb data i b h3 = true
      · have htail : 2 ≤ (fixedQuadBitsEob data (i + 4)).2 := by
          exact fixedQuadBitsEob_len_ge_two data (i + 4)
        simpa [b, h3, hq] using
          (dist1RunBitsTail_len_ge_two b 3 (fixedQuadBitsEob data (i + 4)).1
            (fixedQuadBitsEob data (i + 4)).2 htail)
      · have htail : 2 ≤ (fixedQuadBitsEob data (i + 1)).2 := by
          exact fixedQuadBitsEob_len_ge_two data (i + 1)
        simpa [b, h3, hq] using
          (literalRepeatBitsTail_len_ge_two b 1 (fixedQuadBitsEob data (i + 1)).1
            (fixedQuadBitsEob data (i + 1)).2 htail)
    · dsimp [b]
      have htail : 2 ≤ (fixedQuadBitsEob data (i + 1)).2 := by
        exact fixedQuadBitsEob_len_ge_two data (i + 1)
      simpa [b, h3] using
        (literalRepeatBitsTail_len_ge_two b 1 (fixedQuadBitsEob data (i + 1)).1
          (fixedQuadBitsEob data (i + 1)).2 htail)
  · simp [hlt, fixedLitLenCode]
termination_by data.size - i
decreasing_by
  all_goals omega

def fixedQuadBitsTail (data : Array UInt8) (i tailBits tailLen : Nat) : Nat × Nat :=
  if h : i < data.size then
    let b := data[i]
    if h3 : i + 3 < data.size then
      if quadTailEqb data i b h3 then
        let tail := fixedQuadBitsTail data (i + 4) tailBits tailLen
        dist1RunBitsTail b 3 tail.1 tail.2
      else
        let tail := fixedQuadBitsTail data (i + 1) tailBits tailLen
        literalRepeatBitsTail b 1 tail.1 tail.2
    else
      let tail := fixedQuadBitsTail data (i + 1) tailBits tailLen
      literalRepeatBitsTail b 1 tail.1 tail.2
  else
    let eob := fixedLitLenCode 256
    (reverseBits eob.1 eob.2 ||| (tailBits <<< eob.2), eob.2 + tailLen)
termination_by data.size - i
decreasing_by
  · have hle : data.size - (i + 4) < data.size - i := by
      omega
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle

lemma fixedQuadBitsTail_unfold (data : Array UInt8) (i tailBits tailLen : Nat) :
    fixedQuadBitsTail data i tailBits tailLen =
      (if h : i < data.size then
        let b := data[i]
        if h3 : i + 3 < data.size then
          if quadTailEqb data i b h3 then
            let tail := fixedQuadBitsTail data (i + 4) tailBits tailLen
            dist1RunBitsTail b 3 tail.1 tail.2
          else
            let tail := fixedQuadBitsTail data (i + 1) tailBits tailLen
            literalRepeatBitsTail b 1 tail.1 tail.2
        else
          let tail := fixedQuadBitsTail data (i + 1) tailBits tailLen
          literalRepeatBitsTail b 1 tail.1 tail.2
      else
        let eob := fixedLitLenCode 256
        (reverseBits eob.1 eob.2 ||| (tailBits <<< eob.2), eob.2 + tailLen)) := by
  exact fixedQuadBitsTail.eq_1 (data := data) (i := i) (tailBits := tailBits) (tailLen := tailLen)

lemma fixedQuadBitsTail_len_ge (data : Array UInt8) (i tailBits tailLen : Nat) :
    tailLen ≤ (fixedQuadBitsTail data i tailBits tailLen).2 := by
  classical
  rw [fixedQuadBitsTail_unfold]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    by_cases h3 : i + 3 < data.size
    · dsimp [b]
      by_cases hq : quadTailEqb data i b h3 = true
      · have htail : tailLen ≤ (fixedQuadBitsTail data (i + 4) tailBits tailLen).2 := by
          exact fixedQuadBitsTail_len_ge data (i + 4) tailBits tailLen
        have hmore :
            (fixedQuadBitsTail data (i + 4) tailBits tailLen).2 ≤
              (dist1RunBitsTail b 3 (fixedQuadBitsTail data (i + 4) tailBits tailLen).1
                (fixedQuadBitsTail data (i + 4) tailBits tailLen).2).2 := by
          exact dist1RunBitsTail_len_ge b 3 (fixedQuadBitsTail data (i + 4) tailBits tailLen).1
            (fixedQuadBitsTail data (i + 4) tailBits tailLen).2
        exact le_trans htail (by simpa [b, h3, hq] using hmore)
      · have htail : tailLen ≤ (fixedQuadBitsTail data (i + 1) tailBits tailLen).2 := by
          exact fixedQuadBitsTail_len_ge data (i + 1) tailBits tailLen
        have hmore :
            (fixedQuadBitsTail data (i + 1) tailBits tailLen).2 ≤
              (literalRepeatBitsTail b 1 (fixedQuadBitsTail data (i + 1) tailBits tailLen).1
                (fixedQuadBitsTail data (i + 1) tailBits tailLen).2).2 := by
          exact literalRepeatBitsTail_len_ge b 1 (fixedQuadBitsTail data (i + 1) tailBits tailLen).1
            (fixedQuadBitsTail data (i + 1) tailBits tailLen).2
        exact le_trans htail (by simpa [b, h3, hq] using hmore)
    · dsimp [b]
      have htail : tailLen ≤ (fixedQuadBitsTail data (i + 1) tailBits tailLen).2 := by
        exact fixedQuadBitsTail_len_ge data (i + 1) tailBits tailLen
      have hmore :
          (fixedQuadBitsTail data (i + 1) tailBits tailLen).2 ≤
            (literalRepeatBitsTail b 1 (fixedQuadBitsTail data (i + 1) tailBits tailLen).1
              (fixedQuadBitsTail data (i + 1) tailBits tailLen).2).2 := by
        exact literalRepeatBitsTail_len_ge b 1 (fixedQuadBitsTail data (i + 1) tailBits tailLen).1
          (fixedQuadBitsTail data (i + 1) tailBits tailLen).2
      exact le_trans htail (by simpa [b, h3] using hmore)
  · simp [hlt, fixedLitLenCode, Nat.le_add_left]
termination_by data.size - i
decreasing_by
  all_goals omega

lemma fixedQuadBitsTail_len_ge_two
    (data : Array UInt8) (i tailBits tailLen : Nat) (htail2 : 2 ≤ tailLen) :
    2 ≤ (fixedQuadBitsTail data i tailBits tailLen).2 := by
  exact le_trans htail2 (fixedQuadBitsTail_len_ge data i tailBits tailLen)

lemma byteArrayFromArray_quad4_eq_dist1RunOut
    (data : Array UInt8) (i : Nat) (out : ByteArray)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = true) :
    byteArrayFromArray data i out =
      byteArrayFromArray data (i + 4) (dist1RunOut out data[i] 3) := by
  have h1 : i + 1 < data.size := by omega
  have h2 : i + 2 < data.size := by omega
  have hq' := (quadTailEqb_eq_true (data := data) (i := i) (b := data[i]) (h3 := h3)).1 hq
  have hb1 : data[i + 1]'(by omega) = data[i] := hq'.1
  have hb2 : data[i + 2]'(by omega) = data[i] := hq'.2.1
  have hb3 : data[i + 3]'h3 = data[i] := hq'.2.2
  have hb1' : data[i + 1] = data[i] := by
    simpa using hb1
  have hb2' : data[i + 2] = data[i] := by
    simpa using hb2
  have hb3' : data[i + 3] = data[i] := by
    simpa using hb3
  rw [byteArrayFromArray_unfold]
  simp [h]
  rw [byteArrayFromArray_unfold]
  simp [h1, hb1']
  rw [byteArrayFromArray_unfold]
  simp [h2, hb2']
  rw [byteArrayFromArray_unfold]
  simp [h3, hb3', dist1RunOut, pushRepeat]

lemma fixedQuadOut_eq_byteArrayFromArray (data : Array UInt8) (i : Nat) (out : ByteArray) :
    fixedQuadOut data i out = byteArrayFromArray data i out := by
  classical
  rw [fixedQuadOut_unfold, byteArrayFromArray_unfold]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    by_cases h3 : i + 3 < data.size
    · dsimp [b]
      by_cases hq : quadTailEqb data i b h3 = true
      · have hih : fixedQuadOut data (i + 4) (dist1RunOut out b 3) =
            byteArrayFromArray data (i + 4) (dist1RunOut out b 3) := by
            exact fixedQuadOut_eq_byteArrayFromArray data (i + 4) (dist1RunOut out b 3)
        have hquad :
            byteArrayFromArray data i out =
              byteArrayFromArray data (i + 4) (dist1RunOut out b 3) := by
          simpa [b] using
            (byteArrayFromArray_quad4_eq_dist1RunOut (data := data) (i := i) (out := out)
              (h := hlt) (h3 := h3) (hq := by simpa [b] using hq))
        have hquad1 :
            byteArrayFromArray data (i + 1) (out.push b) =
              byteArrayFromArray data (i + 4) (dist1RunOut out b 3) := by
          have htmp : byteArrayFromArray data (i + 1) (out.push b) = byteArrayFromArray data i out := by
            symm
            rw [byteArrayFromArray_unfold]
            simp [hlt, b]
          exact htmp.trans hquad
        simpa [b, h3, hq, hquad1] using hih
      · have hih : fixedQuadOut data (i + 1) (out.push b) =
            byteArrayFromArray data (i + 1) (out.push b) := by
            exact fixedQuadOut_eq_byteArrayFromArray data (i + 1) (out.push b)
        simpa [b, h3, hq] using hih
    · dsimp [b]
      have hih : fixedQuadOut data (i + 1) (out.push b) =
          byteArrayFromArray data (i + 1) (out.push b) := by
          exact fixedQuadOut_eq_byteArrayFromArray data (i + 1) (out.push b)
      simpa [b, h3] using hih
  · simp [hlt]
termination_by data.size - i
decreasing_by
  all_goals omega

lemma fixedQuadOut_empty (data : Array UInt8) :
    fixedQuadOut data 0 ByteArray.empty = ByteArray.mk data := by
  calc
    fixedQuadOut data 0 ByteArray.empty = byteArrayFromArray data 0 ByteArray.empty := by
      simpa using fixedQuadOut_eq_byteArrayFromArray data 0 ByteArray.empty
    _ = ByteArray.mk data := by
      simpa using byteArrayFromArray_empty (data := data)

lemma fixedQuadBitsTail_zero_zero (data : Array UInt8) (i : Nat) :
    fixedQuadBitsTail data i 0 0 = fixedQuadBitsEob data i := by
  classical
  rw [fixedQuadBitsTail_unfold, fixedQuadBitsEob_unfold]
  by_cases hlt : i < data.size
  · simp [hlt]
    let b := data[i]
    by_cases h3 : i + 3 < data.size
    · dsimp [b]
      by_cases hq : quadTailEqb data i b h3 = true
      · simpa [b, h3, hq, fixedQuadBitsTail_zero_zero data (i + 4)]
      · simpa [b, h3, hq, fixedQuadBitsTail_zero_zero data (i + 1)]
    · dsimp [b]
      simpa [b, h3, fixedQuadBitsTail_zero_zero data (i + 1)]
  · simp [hlt, fixedLitLenCode]
termination_by data.size - i
decreasing_by
  all_goals omega

lemma fixedQuadBitsEob_of_quad
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = true) :
    fixedQuadBitsEob data i =
      dist1RunBitsTail data[i] 3 (fixedQuadBitsEob data (i + 4)).1 (fixedQuadBitsEob data (i + 4)).2 := by
  rw [fixedQuadBitsEob_unfold]
  simp [h, h3, hq]

lemma fixedQuadStepsEob_of_quad
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = true) :
    fixedQuadStepsEob data i = dist1RunSteps 3 + fixedQuadStepsEob data (i + 4) := by
  rw [fixedQuadStepsEob_unfold]
  simp [h, h3, hq]

lemma fixedQuadOut_of_quad
    (data : Array UInt8) (i : Nat) (out : ByteArray)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = true) :
    fixedQuadOut data i out = fixedQuadOut data (i + 4) (dist1RunOut out data[i] 3) := by
  rw [fixedQuadOut_unfold]
  simp [h, h3, hq]

lemma fixedQuadBitsEob_of_lit_hqFalse
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = false) :
    fixedQuadBitsEob data i =
      literalRepeatBitsTail data[i] 1 (fixedQuadBitsEob data (i + 1)).1 (fixedQuadBitsEob data (i + 1)).2 := by
  rw [fixedQuadBitsEob_unfold]
  simp [h, h3, hq]

lemma fixedQuadStepsEob_of_lit_hqFalse
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = false) :
    fixedQuadStepsEob data i = 1 + fixedQuadStepsEob data (i + 1) := by
  rw [fixedQuadStepsEob_unfold]
  simp [h, h3, hq]

lemma fixedQuadOut_of_lit_hqFalse
    (data : Array UInt8) (i : Nat) (out : ByteArray)
    (h : i < data.size) (h3 : i + 3 < data.size)
    (hq : quadTailEqb data i data[i] h3 = false) :
    fixedQuadOut data i out = fixedQuadOut data (i + 1) (out.push data[i]) := by
  rw [fixedQuadOut_unfold]
  simp [h, h3, hq]

lemma fixedQuadBitsEob_of_lit_noh3
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : ¬ i + 3 < data.size) :
    fixedQuadBitsEob data i =
      literalRepeatBitsTail data[i] 1 (fixedQuadBitsEob data (i + 1)).1 (fixedQuadBitsEob data (i + 1)).2 := by
  rw [fixedQuadBitsEob_unfold]
  simp [h, h3]

lemma fixedQuadStepsEob_of_lit_noh3
    (data : Array UInt8) (i : Nat)
    (h : i < data.size) (h3 : ¬ i + 3 < data.size) :
    fixedQuadStepsEob data i = 1 + fixedQuadStepsEob data (i + 1) := by
  rw [fixedQuadStepsEob_unfold]
  simp [h, h3]

lemma fixedQuadOut_of_lit_noh3
    (data : Array UInt8) (i : Nat) (out : ByteArray)
    (h : i < data.size) (h3 : ¬ i + 3 < data.size) :
    fixedQuadOut data i out = fixedQuadOut data (i + 1) (out.push data[i]) := by
  rw [fixedQuadOut_unfold]
  simp [h, h3]

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
