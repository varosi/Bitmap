import Bitmap.Lemmas.Png.FixedLiteral
import Bitmap.Png
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.ByteArray.Lemmas
import Init.Data.Range.Lemmas
import Init.Data.UInt.Lemmas
import Batteries.Data.ByteArray

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

def byteArrayFromArray (data : Array UInt8) (i : Nat) (out : ByteArray) : ByteArray :=
  if h : i < data.size then
    byteArrayFromArray data (i + 1) (out.push data[i])
  else
    out
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  have hle : data.size - (i + 1) < data.size - i := by
    exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
  exact hle

lemma byteArrayFromArray_unfold (data : Array UInt8) (i : Nat) (out : ByteArray) :
    byteArrayFromArray data i out =
      (if h : i < data.size then
        byteArrayFromArray data (i + 1) (out.push data[i])
      else
        out) := by
  exact byteArrayFromArray.eq_1 (data := data) (i := i) (out := out)

-- Size of the byteArrayFromArray output.
lemma byteArrayFromArray_size (data : Array UInt8) (i : Nat) (out : ByteArray) :
    (byteArrayFromArray data i out).size = out.size + (data.size - i) := by
  classical
  have hk :
      ∀ k, ∀ i out, data.size - i = k →
        (byteArrayFromArray data i out).size = out.size + k := by
    intro k
    induction k with
    | zero =>
        intro i out hk
        have hle : data.size ≤ i := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ i < data.size := not_lt_of_ge hle
        simp [byteArrayFromArray, hlt]
    | succ k ih =>
        intro i out hk
        have hlt : i < data.size := by
          have hpos : 0 < data.size - i := by omega
          exact (Nat.sub_pos_iff_lt).1 hpos
        have hk' : data.size - (i + 1) = k := by omega
        have hsize :=
          ih (i := i + 1) (out := out.push data[i]) hk'
        have hpush : (out.push data[i]).size = out.size + 1 := by
          simp [ByteArray.size_push]
        -- unfold once and simplify
        calc
          (byteArrayFromArray data i out).size
              = (byteArrayFromArray data (i + 1) (out.push data[i])).size := by
                  rw [byteArrayFromArray_unfold]
                  simp [hlt]
          _ = (out.push data[i]).size + k := by
                  exact hsize
          _ = out.size + Nat.succ k := by
                  simp [hpush, Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
  exact hk (data.size - i) i out rfl

-- Reads from the prefix are preserved.
lemma byteArrayFromArray_get_lt (data : Array UInt8) (i : Nat) (out : ByteArray)
    (j : Nat) (hj : j < out.size) :
    (byteArrayFromArray data i out)[j]'(by
        have hsize := byteArrayFromArray_size (data := data) (i := i) (out := out)
        have : out.size ≤ (byteArrayFromArray data i out).size := by
          simpa [hsize, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            Nat.le_add_right out.size (data.size - i)
        exact lt_of_lt_of_le hj this) =
      out[j]'hj := by
  classical
  have hk :
      ∀ k, ∀ i out j, data.size - i = k → (hj : j < out.size) →
        (byteArrayFromArray data i out)[j]'(by
            have hsize := byteArrayFromArray_size (data := data) (i := i) (out := out)
            have : out.size ≤ (byteArrayFromArray data i out).size := by
              simpa [hsize, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                Nat.le_add_right out.size (data.size - i)
            exact lt_of_lt_of_le hj this) =
          out[j]'hj := by
    intro k
    induction k with
    | zero =>
        intro i out j hk hj
        have hle : data.size ≤ i := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ i < data.size := not_lt_of_ge hle
        simp [byteArrayFromArray, hlt]
    | succ k ih =>
        intro i out j hk hj
        have hlt : i < data.size := by
          have hpos : 0 < data.size - i := by omega
          exact (Nat.sub_pos_iff_lt).1 hpos
        have hk' : data.size - (i + 1) = k := by omega
        have hj' : j < (out.push data[i]).size := by
          have : j < out.size + 1 := by
            exact lt_trans hj (Nat.lt_succ_self out.size)
          simpa [ByteArray.size_push] using this
        have hrec := ih (i := i + 1) (out := out.push data[i]) (j := j) hk' hj'
        -- use prefix preservation of push
        have hpush :
            (out.push data[i])[j]'(by
                simpa [ByteArray.size_push] using hj') = out[j]'hj := by
          simpa using (ByteArray.get_push_lt out data[i] j hj)
        -- unfold one step
        have hbaa :
            byteArrayFromArray data i out =
              byteArrayFromArray data (i + 1) (out.push data[i]) := by
          rw [byteArrayFromArray_unfold]
          simp [hlt]
        simp [hbaa, hrec, hpush]
  exact hk (data.size - i) i out j rfl hj

-- Reads from the appended suffix match the array.
lemma byteArrayFromArray_get_ge (data : Array UInt8) (i : Nat) (out : ByteArray)
    (j : Nat) (hj : j < (byteArrayFromArray data i out).size) (hge : out.size ≤ j) :
    (byteArrayFromArray data i out)[j]'hj =
      data[i + (j - out.size)]'(by
        -- show the index is within bounds
        have hsize := byteArrayFromArray_size (data := data) (i := i) (out := out)
        have hlt : j < out.size + (data.size - i) := by simpa [hsize] using hj
        have hlt' : j - out.size < data.size - i := by
          exact Nat.sub_lt_left_of_lt_add hge hlt
        omega) := by
  classical
  have hk :
      ∀ k, ∀ i out j, data.size - i = k → (hj : j < (byteArrayFromArray data i out).size) →
        (hge : out.size ≤ j) →
          (byteArrayFromArray data i out)[j]'(by
              have hsize := byteArrayFromArray_size (data := data) (i := i) (out := out)
              have hlt : j < out.size + (data.size - i) := by simpa [hsize] using hj
              have hlt' : j - out.size < data.size - i := by
                exact Nat.sub_lt_left_of_lt_add hge hlt
              omega) =
            data[i + (j - out.size)]'(by
              have hsize := byteArrayFromArray_size (data := data) (i := i) (out := out)
              have hlt : j < out.size + (data.size - i) := by simpa [hsize] using hj
              have hlt' : j - out.size < data.size - i := by
                exact Nat.sub_lt_left_of_lt_add hge hlt
              omega) := by
    intro k
    induction k with
    | zero =>
        intro i out j hk hj hge
        have hle : data.size ≤ i := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ i < data.size := not_lt_of_ge hle
        have hj' : j < out.size := by
          simpa [byteArrayFromArray, hlt] using hj
        have : False := by omega
        exact (False.elim this)
    | succ k ih =>
        intro i out j hk hj hge
        have hlt : i < data.size := by
          have hpos : 0 < data.size - i := by omega
          exact (Nat.sub_pos_iff_lt).1 hpos
        have hk' : data.size - (i + 1) = k := by omega
        -- unfold one step
        by_cases hj' : j < (out.push data[i]).size
        · -- j is within the pushed prefix
          have hcase : j = out.size := by
            have hlt' : j < out.size + 1 := by simpa [ByteArray.size_push] using hj'
            have hge' : out.size ≤ j := hge
            omega
          subst hcase
          have hget :
              (out.push data[i])[out.size]'(by
                  simpa [ByteArray.size_push] using Nat.lt_succ_self out.size) = data[i] := by
            simpa using (ByteArray.get_push_eq out data[i])
          -- recurse returns out.push at this index
          have hrec := byteArrayFromArray_get_lt (data := data) (i := i + 1)
            (out := out.push data[i]) (j := out.size)
            (by simpa [ByteArray.size_push] using Nat.lt_succ_self out.size)
          have hbaa :
              byteArrayFromArray data i out =
                byteArrayFromArray data (i + 1) (out.push data[i]) := by
            rw [byteArrayFromArray_unfold]
            simp [hlt]
          -- simplify index arithmetic
          simp [hbaa, hget, Nat.sub_self, hrec]
        · -- j is in the suffix beyond the pushed element
          have hge' : (out.push data[i]).size ≤ j := by
            have hlt' : ¬ j < (out.push data[i]).size := hj'
            exact Nat.le_of_not_gt hlt'
          have hj'' : j < (byteArrayFromArray data (i + 1) (out.push data[i])).size := by
            rw [byteArrayFromArray_unfold] at hj
            simpa [hlt] using hj
          have hrec :=
            ih (i := i + 1) (out := out.push data[i]) (j := j) hk' hj'' hge'
          -- simplify index arithmetic
          have hbaa :
              byteArrayFromArray data i out =
                byteArrayFromArray data (i + 1) (out.push data[i]) := by
            rw [byteArrayFromArray_unfold]
            simp [hlt]
          have hsub : j - (out.push data[i]).size = j - out.size - 1 := by
            simp [ByteArray.size_push, Nat.sub_sub]
          have hpos : 0 < j - out.size := by
            have hge'' : out.size + 1 ≤ j := by
              simpa [ByteArray.size_push] using hge'
            have hlt' : out.size < j := by
              exact lt_of_lt_of_le (Nat.lt_succ_self out.size) hge''
            exact Nat.sub_pos_of_lt hlt'
          have hidx : i + (1 + (j - (out.size + 1))) = i + (j - out.size) := by
            have hpos' : 1 ≤ j - out.size := (Nat.succ_le_iff).2 hpos
            have hstep : 1 + (j - out.size - 1) = j - out.size := by
              calc
                1 + (j - out.size - 1) = (j - out.size - 1) + 1 := by
                  simp [Nat.add_comm]
                _ = j - out.size := by
                  simpa using (Nat.sub_add_cancel hpos')
            calc
              i + (1 + (j - (out.size + 1)))
                  = i + (1 + (j - out.size - 1)) := by
                      simp [Nat.sub_sub]
              _ = i + (j - out.size) := by
                      simp [hstep]
          simp [hbaa, hrec, ByteArray.size_push, hsub, hidx, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]
  exact hk (data.size - i) i out j rfl hj hge

-- The accumulator-based builder matches the original array (empty prefix).
lemma byteArrayFromArray_empty (data : Array UInt8) :
    byteArrayFromArray data 0 ByteArray.empty = ByteArray.mk data := by
  classical
  -- reduce to array equality
  apply (ByteArray.ext_iff).2
  apply (Array.ext_iff).2
  constructor
  · -- sizes agree
    have hsize := byteArrayFromArray_size (data := data) (i := 0) (out := ByteArray.empty)
    simpa using hsize
  · intro i hi1 hi2
    have hget :=
      byteArrayFromArray_get_ge (data := data) (i := 0) (out := ByteArray.empty)
        (j := i) (hj := by simpa using hi1) (hge := by simp)
    simpa using hget

-- Bit encoding for a literal sequence followed by EOB.
def fixedLitBitsEob (data : Array UInt8) (i : Nat) : Nat × Nat :=
  if h : i < data.size then
    let b := data[i]
    let codeLen := fixedLitLenCode b.toNat
    let code := codeLen.1
    let len := codeLen.2
    let rest := fixedLitBitsEob data (i + 1)
    let restBits := rest.1
    let restLen := rest.2
    (reverseBits code len ||| (restBits <<< len), len + restLen)
  else
    let eob := fixedLitLenCode 256
    (reverseBits eob.1 eob.2, eob.2)
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  have hle : data.size - (i + 1) < data.size - i := by
    exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
  exact hle

-- The bit-length encoding is at least the number of symbols (including EOB).
lemma fixedLitBitsEob_len_ge (data : Array UInt8) (i : Nat) :
    data.size - i + 1 ≤ (fixedLitBitsEob data i).2 := by
  classical
  have hk :
      ∀ k, ∀ i, data.size - i = k → k + 1 ≤ (fixedLitBitsEob data i).2 := by
    intro k
    induction k with
    | zero =>
        intro i hk
        have hle : data.size ≤ i := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ i < data.size := not_lt_of_ge hle
        -- only the EOB symbol remains
        simpa [fixedLitBitsEob, hlt] using (by decide : 1 ≤ (fixedLitLenCode 256).2)
    | succ k ih =>
        intro i hk
        have hlt : i < data.size := by
          have hpos : 0 < data.size - i := by omega
          exact (Nat.sub_pos_iff_lt).1 hpos
        have hk' : data.size - (i + 1) = k := by omega
        let b := data[i]
        let codeLen := fixedLitLenCode b.toNat
        let len := codeLen.2
        let rest := fixedLitBitsEob data (i + 1)
        let restLen := rest.2
        have hrest : k + 1 ≤ restLen := ih (i := i + 1) hk'
        have hlen : 1 ≤ len := by
          have hsym : b.toNat < 288 := by
            have hlt' : b.toNat < 256 := by
              simpa using (UInt8.toNat_lt b)
            exact lt_trans hlt' (by decide)
          simpa [len, codeLen] using (fixedLitLenCode_len_pos b.toNat hsym)
        have hsum : k + 2 ≤ len + restLen := by
          have h := Nat.add_le_add hrest hlen
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
        -- unfold once and simplify
        rw [fixedLitBitsEob]
        simpa [hlt, b, codeLen, len, rest, restLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum
  exact hk (data.size - i) i rfl

-- Writing the fixed literal stream (with EOB) matches the concatenated bit encoding.
lemma fixedLitBitsEob_writeBits (data : Array UInt8) (i : Nat) (bw : BitWriter) :
    let bitsLen := fixedLitBitsEob data i
    let bits := bitsLen.1
    let len := bitsLen.2
    let bw' := BitWriter.writeBits bw bits len
    let bw1 := deflateFixedAux data i bw
    let eob := fixedLitLenCode 256
    bw' = BitWriter.writeBits bw1 (reverseBits eob.1 eob.2) eob.2 := by
  classical
  have hk :
      ∀ k, ∀ i bw, data.size - i = k →
        let bitsLen := fixedLitBitsEob data i
        let bits := bitsLen.1
        let len := bitsLen.2
        let bw' := BitWriter.writeBits bw bits len
        let bw1 := deflateFixedAux data i bw
        let eob := fixedLitLenCode 256
        bw' = BitWriter.writeBits bw1 (reverseBits eob.1 eob.2) eob.2 := by
    intro k
    induction k with
    | zero =>
        intro i bw hk
        have hle : data.size ≤ i := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ i < data.size := not_lt_of_ge hle
        simp [fixedLitBitsEob, hlt, deflateFixedAux, hlt]
    | succ k ih =>
        intro i bw hk
        have hlt : i < data.size := by
          have hpos : 0 < data.size - i := by omega
          exact (Nat.sub_pos_iff_lt).1 hpos
        have hk' : data.size - (i + 1) = k := by omega
        -- unpack the head symbol
        let b := data[i]
        let codeLen := fixedLitLenCode b.toNat
        let code := codeLen.1
        let len := codeLen.2
        let bits := reverseBits code len
        let rest := fixedLitBitsEob data (i + 1)
        let restBits := rest.1
        let restLen := rest.2
        have ih' :=
          ih (i := i + 1) (bw := BitWriter.writeBits bw bits len) hk'
        -- combine using concatenation
        have hbits : bits < 2 ^ len := by
          simpa [bits] using (reverseBits_lt code len)
        have hconcat :
            BitWriter.writeBits bw (bits ||| (restBits <<< len)) (len + restLen) =
              BitWriter.writeBits (BitWriter.writeBits bw bits len) restBits restLen := by
          simpa using (writeBits_concat bw bits restBits len restLen hbits)
        have hbitsLen :
            fixedLitBitsEob data i = (bits ||| (restBits <<< len), len + restLen) := by
          rw [fixedLitBitsEob]
          simp [hlt, b, codeLen, code, len, bits, rest, restBits, restLen]
        have hbw1 :
            deflateFixedAux data i bw =
              deflateFixedAux data (i + 1) (BitWriter.writeBits bw bits len) := by
          rw [deflateFixedAux]
          simp [hlt, b, codeLen, code, len, bits]
        -- unfold and finish
        simp [hbitsLen, hbw1, hconcat, ih', bits, rest, restBits, restLen]
  exact hk (data.size - i) i bw rfl

-- Decoding a fixed literal block recovers the original bytes.
lemma decodeFixedLiteralBlock_fixedLitBitsEob (data : Array UInt8) (i : Nat) (bw : BitWriter)
    (out : ByteArray) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsLen := fixedLitBitsEob data i
    let bits := bitsLen.1
    let len := bitsLen.2
    let bw' := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
    decodeFixedLiteralBlock br out =
      some (BitWriter.readerAt (BitWriter.writeBits bw bits len) bw'.flush
        (by
          -- exact bound: data is the flush itself
          simpa [bw'] using
            (le_rfl : (BitWriter.writeBits bw bits len).flush.size ≤
              (BitWriter.writeBits bw bits len).flush.size))
        (bitPos_lt_8_writeBits bw bits len hbit),
    byteArrayFromArray data i out) := by
  classical
  have hk :
      ∀ k, ∀ i bw out (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove), data.size - i = k →
        ∀ fuel, k + 1 ≤ fuel →
        let bitsLen := fixedLitBitsEob data i
        let bits := bitsLen.1
        let len := bitsLen.2
        let bw' := BitWriter.writeBits bw bits len
        let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
        decodeFixedLiteralBlockFuel fuel br out =
          some (BitWriter.readerAt (BitWriter.writeBits bw bits len) bw'.flush
            (by
              -- exact bound: data is the flush itself
              simpa [bw'] using
                (le_rfl : (BitWriter.writeBits bw bits len).flush.size ≤
                  (BitWriter.writeBits bw bits len).flush.size))
            (bitPos_lt_8_writeBits bw bits len hbit),
            byteArrayFromArray data i out) := by
    intro k
    induction k with
    | zero =>
        intro i bw out hbit hcur hk fuel hfuel
        cases fuel with
        | zero =>
            have : (1 : Nat) ≤ 0 := by simpa using hfuel
            exact (False.elim (Nat.not_succ_le_zero 0 this))
        | succ fuel =>
            have hle : data.size ≤ i := Nat.le_of_sub_eq_zero hk
            have hlt : ¬ i < data.size := not_lt_of_ge hle
            -- base case: only EOB
            have hsym : (256 : Nat) < 288 := by decide
            -- use decodeFixedLiteralSym on the EOB bits (no rest)
            have hdecode :=
              decodeFixedLiteralSym_readerAt_writeBits' (bw := bw) (sym := 256)
                (restBits := 0) (restLen := 0) hsym hbit hcur
            simp [fixedLitBitsEob, hlt] at hdecode
            -- unfold and finish
            simp [decodeFixedLiteralBlockFuel, fixedLitBitsEob, hlt, byteArrayFromArray, hdecode]
    | succ k ih =>
        intro i bw out hbit hcur hk fuel hfuel
        cases fuel with
        | zero =>
            have : (k + 2) ≤ 0 := by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfuel
            exact (False.elim (Nat.not_succ_le_zero _ this))
        | succ fuel =>
            have hlt : i < data.size := by
              have hpos : 0 < data.size - i := by omega
              exact (Nat.sub_pos_iff_lt).1 hpos
            have hk' : data.size - (i + 1) = k := by omega
            let b := data[i]
            let codeLen := fixedLitLenCode b.toNat
            let code := codeLen.1
            let len := codeLen.2
            let bits := reverseBits code len
            let rest := fixedLitBitsEob data (i + 1)
            let restBits := rest.1
            let restLen := rest.2
            let bitsTot := bits ||| (restBits <<< len)
            let lenTot := len + restLen
            let bw' := BitWriter.writeBits bw bitsTot lenTot
            let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
            have hbitsLen : fixedLitBitsEob data i = (bitsTot, lenTot) := by
              rw [fixedLitBitsEob]
              simp [hlt, bitsTot, lenTot, b, codeLen, code, len, bits, rest, restBits, restLen]
            have hsym : b.toNat < 288 := by
              have hlt' : b.toNat < 256 := by
                simpa using (UInt8.toNat_lt b)
              exact lt_trans hlt' (by decide)
            have hdecode :=
              decodeFixedLiteralSym_readerAt_writeBits' (bw := bw) (sym := b.toNat)
                (restBits := restBits) (restLen := restLen) hsym hbit hcur
            -- identify the reader at the rest stream
            have hbits : bits < 2 ^ len := by
              simpa [bits] using (reverseBits_lt code len)
            have hconcat :
                BitWriter.writeBits bw bitsTot lenTot =
                  BitWriter.writeBits (BitWriter.writeBits bw bits len) restBits restLen := by
              simpa [bitsTot, lenTot] using (writeBits_concat bw bits restBits len restLen hbits)
            have hmod : bitsTot % 2 ^ len = bits := by
              have hmod' : bitsTot % 2 ^ len = bits % 2 ^ len := by
                simpa [bitsTot] using
                  (mod_two_pow_or_shift (a := bits) (b := restBits) (k := len) (len := len) (hk := le_rfl))
              have hbitsmod : bits % 2 ^ len = bits := by
                exact Nat.mod_eq_of_lt hbits
              simpa [hbitsmod] using hmod'
            have hwriteBits : BitWriter.writeBits bw bitsTot len = BitWriter.writeBits bw bits len := by
              calc
                BitWriter.writeBits bw bitsTot len
                    = BitWriter.writeBits bw (bitsTot % 2 ^ len) len := by
                        simpa using (writeBits_mod bw bitsTot len)
                _ = BitWriter.writeBits bw bits len := by
                        simp [hmod]
            -- apply the IH to the rest
            have hih :=
              ih (i := i + 1) (bw := BitWriter.writeBits bw bits len) (out := out.push (u8 b.toNat))
                (hbit := bitPos_lt_8_writeBits bw bits len hbit)
                (hcur := curClearAbove_writeBits bw bits len hbit hcur) hk' fuel (by
                  -- from k + 2 ≤ Nat.succ fuel
                  have : k + 2 ≤ Nat.succ fuel := by
                    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfuel
                  exact (Nat.succ_le_succ_iff.mp this))
            -- rewrite `hih` to use the combined writer/flush
            have hih' :
                decodeFixedLiteralBlockFuel fuel
                    (BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
                      (by
                        have hk : len ≤ lenTot := by omega
                        simpa [bw', lenTot] using
                          (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
                      (bitPos_lt_8_writeBits bw bitsTot len hbit))
                    (out.push (u8 b.toNat)) =
                  some (BitWriter.readerAt (BitWriter.writeBits bw bitsTot lenTot) bw'.flush
                    (by
                      simpa [bw'] using
                        (le_rfl : (BitWriter.writeBits bw bitsTot lenTot).flush.size ≤
                          (BitWriter.writeBits bw bitsTot lenTot).flush.size))
                    (bitPos_lt_8_writeBits bw bitsTot lenTot hbit),
                    byteArrayFromArray data (i + 1) (out.push (u8 b.toNat))) := by
              simpa [bitsTot, lenTot, bw', hconcat, hwriteBits] using hih
            -- now combine
            have hdecode' := by
              simpa [bitsTot, lenTot, bw', br, codeLen, code, len, bits, rest, restBits, restLen] using hdecode
            -- unfold and finish
            have hlt256 : b.toNat < 256 := by
              simpa using (UInt8.toNat_lt b)
            simp [decodeFixedLiteralBlockFuel, hbitsLen]
            rw [hdecode']
            simp [hlt256]
            have hstep : byteArrayFromArray data i out =
                byteArrayFromArray data (i + 1) (out.push (u8 b.toNat)) := by
              rw [byteArrayFromArray_unfold]
              simp [hlt, b, u8]
            simpa [hstep] using hih'
  -- instantiate the fuel-bound proof for the actual reader
  let bitsLen := fixedLitBitsEob data i
  let bits := bitsLen.1
  let len := bitsLen.2
  let bw' := BitWriter.writeBits bw bits len
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
  have hlen_ge : data.size - i + 1 ≤ len := by
    simpa [bitsLen, len] using (fixedLitBitsEob_len_ge (data := data) (i := i))
  have hlen_le : len ≤ br.data.size * 8 := by
    have hlen_le_bitcount : len ≤ bw'.bitCount := by
      have h := Nat.le_add_left len bw.bitCount
      simpa [bw', bitCount_writeBits, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have hbitcount_le : bw'.bitCount ≤ bw'.flush.size * 8 := by
      exact (flush_size_mul_ge_bitCount (bw := bw') (hbit := bw'.hbit))
    have hlen_le' : len ≤ bw'.flush.size * 8 := le_trans hlen_le_bitcount hbitcount_le
    simpa [br] using hlen_le'
  have hfuel : data.size - i + 1 ≤ br.data.size * 8 := le_trans hlen_ge hlen_le
  have hmain :=
    hk (data.size - i) i bw out hbit hcur rfl (br.data.size * 8) hfuel
  simpa [decodeFixedLiteralBlock, bitsLen, bits, len, bw', br] using hmain

set_option maxHeartbeats 4000000 in
-- Deflate-fixed output equals writing the fixed literal stream after the block header.
lemma deflateFixed_eq_writeBits (raw : ByteArray) :
    let bw0 := BitWriter.empty
    let bw1 := bw0.writeBits 1 1
    let bw2 := bw1.writeBits 1 2
    let bitsLen := fixedLitBitsEob raw.data 0
    deflateFixed raw = (BitWriter.writeBits bw2 bitsLen.1 bitsLen.2).flush := by
  classical
  unfold deflateFixed
  -- unfold header writers
  simp
  -- relate deflateFixedAux + EOB to fixedLitBitsEob
  have hbits :=
    fixedLitBitsEob_writeBits (data := raw.data) (i := 0)
      (bw := BitWriter.writeBits (BitWriter.writeBits BitWriter.empty 1 1) 1 2)
  -- rewrite the writer equality and flush
  simpa using (congrArg BitWriter.flush hbits).symm


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
