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


-- Reading one bit advances the bit index by one.
-- Re-export: reading one bit advances the bit index by one.
lemma bitIndex_readBit (br : BitReader) (h : br.bytePos < br.data.size) :
    (BitReader.readBit br).2.bitIndex = br.bitIndex + 1 := by
  unfold BitReader.readBit BitReader.bitIndex
  have hne : br.bytePos ≠ br.data.size := ne_of_lt h
  by_cases hnext : br.bitPos + 1 = 8
  · calc
      (BitReader.readBit br).2.bitIndex
          = (br.bytePos + 1) * 8 := by
              simp [BitReader.readBit, BitReader.bitIndex, hne, hnext]
      _ = br.bytePos * 8 + (br.bitPos + 1) := by
              simp [Nat.add_mul, hnext, Nat.add_comm]
      _ = br.bitIndex + 1 := by
              simp [BitReader.bitIndex, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · simp [hne, hnext, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

-- Reading a bit does not mutate the underlying data buffer.
-- Re-export: reading a bit does not change the underlying data.
lemma readBit_data (br : BitReader) (h : br.bytePos < br.data.size) :
    (br.readBit).2.data = br.data := by
  unfold BitReader.readBit
  have hne : br.bytePos ≠ br.data.size := ne_of_lt h
  by_cases hnext : br.bitPos + 1 = 8 <;> simp [hne, hnext]

-- `get` agrees with the `[]` notation for byte arrays.
lemma byteArray_get_eq_getElem (a : ByteArray) (i : Nat) (h : i < a.size) :
    a.get i h = a[i]'h := rfl

-- `ByteArray.get` is proof-irrelevant for bounds.
lemma byteArray_get_proof_irrel {a : ByteArray} {i : Nat} (h1 h2 : i < a.size) :
    a.get i h1 = a.get i h2 := by
  cases a
  rfl

-- Setting a byte does not change the buffer size.
@[simp] lemma byteArray_size_set
    {bs : ByteArray} {i : Nat} (h : i < bs.size) {v : UInt8} :
    (bs.set i v h).size = bs.size := by
  cases bs with
  | mk arr =>
      simp [ByteArray.set, ByteArray.size, Array.size_set]

-- Getting the byte just set yields the new value.
@[simp] lemma byteArray_get_set_self
    {bs : ByteArray} {i : Nat} (h : i < bs.size) {v : UInt8} :
    (bs.set i v h).get i (by simpa [byteArray_size_set] using h) = v := by
  cases bs with
  | mk arr =>
      simp [ByteArray.set, ByteArray.get]

-- Getting the byte just set yields the new value (explicit bounds).
@[simp] lemma byteArray_get_set_self'
    {bs : ByteArray} {i : Nat} (h : i < bs.size) {v : UInt8}
    (h' : i < (bs.set i v h).size) :
    (bs.set i v h).get i h' = v := by
  cases bs with
  | mk arr =>
      simp [ByteArray.set, ByteArray.get]

-- Getting a different index after setting preserves the old value (explicit bounds).
lemma byteArray_get_set_ne'
    {bs : ByteArray} {i j : Nat} (hi : i < bs.size) (hj : j < bs.size)
    (hij : i ≠ j) {v : UInt8} (h' : j < (bs.set i v hi).size) :
    (bs.set i v hi).get j h' = bs.get j hj := by
  cases bs with
  | mk arr =>
      simpa [ByteArray.set, ByteArray.get] using
        (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj) (h := hij))

-- Getting the byte just set yields the new value (alternate proof of bounds).
-- `getElem` is proof-irrelevant for ByteArrays.
@[simp] lemma byteArray_getElem_eq {bs : ByteArray} {i : Nat} (h1 h2 : i < bs.size) :
    bs[i]'h1 = bs[i]'h2 := by
  rfl


-- Extracting a prefix from an append only depends on the left chunk.
lemma byteArray_extract_append_prefix (a b : ByteArray) (n : Nat) (hn : n ≤ a.size) :
    (a ++ b).extract 0 n = a.extract 0 n := by
  have := (ByteArray.extract_append (as := a) (bs := b) (i := 0) (j := n))
  -- The right extract is empty since `n ≤ a.size`.
  simpa [Nat.sub_eq_zero_of_le hn] using this

-- Extracting a slice that lies entirely in the left chunk ignores the right chunk.
lemma byteArray_extract_append_left (a b : ByteArray) (i j : Nat)
    (hi : i ≤ a.size) (hj : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  have := (ByteArray.extract_append (as := a) (bs := b) (i := i) (j := j))
  -- Both subtractions are zero since the slice stays within `a`.
  simpa [Nat.sub_eq_zero_of_le hi, Nat.sub_eq_zero_of_le hj] using this

-- Splitting a byte array into prefix/suffix extracts and re-appending yields the original.
lemma byteArray_extract_split (a : ByteArray) (n : Nat) (hn : n ≤ a.size) :
    a.extract 0 n ++ a.extract n a.size = a := by
  ext i hi
  · -- size goal
    simp
  · -- element goal
    by_cases hlt : i < n
    · have hleft : i < (a.extract 0 n).size := by
        simp [ByteArray.size_extract, Nat.min_eq_left hn, hlt]
      have hget_left :
          (a.extract 0 n ++ a.extract n a.size)[i] = (a.extract 0 n)[i] := by
        exact
          (ByteArray.get_append_left (a := a.extract 0 n) (b := a.extract n a.size)
            (i := i) hleft)
      have hget_extract : (a.extract 0 n)[i] = a[i] := by
        calc
          (a.extract 0 n)[i] = a[0 + i] := by
            exact
              (ByteArray.get_extract (a := a) (start := 0) (stop := n) (i := i) hleft)
          _ = a[i] := by simp
      calc
        (a.extract 0 n ++ a.extract n a.size)[i] = (a.extract 0 n)[i] := hget_left
        _ = a[i] := hget_extract
    · have hge : n ≤ i := Nat.le_of_not_lt hlt
      have hright : i - n < (a.extract n a.size).size := by
        have hi' : i < a.size := by
          have hi' := hi
          simp at hi'
          exact hi'
        have hlt' : i - n < a.size - n := Nat.sub_lt_sub_right hge hi'
        have hsize : (a.extract n a.size).size = a.size - n := by
          simp [ByteArray.size_extract]
        rw [hsize]
        exact hlt'
      have hget_right :
          (a.extract 0 n ++ a.extract n a.size)[i] =
            (a.extract n a.size)[i - n] := by
        have hle : (a.extract 0 n).size ≤ i := by
          simp [ByteArray.size_extract, Nat.min_eq_left hn, hge]
        have hget' :=
          (ByteArray.get_append_right (a := a.extract 0 n) (b := a.extract n a.size)
            (i := i) (hle := hle) (h := hi))
        have hsize_left : (a.extract 0 n).size = n := by
          simp [ByteArray.size_extract, Nat.min_eq_left hn]
        calc
          (a.extract 0 n ++ a.extract n a.size)[i] =
              (a.extract n a.size)[i - (a.extract 0 n).size] := hget'
          _ = (a.extract n a.size)[i - n] := by
              simp [hsize_left]
      have hget_extract : (a.extract n a.size)[i - n] = a[i] := by
        have hi' : i < a.size := by
          have hi' := hi
          simp at hi'
          exact hi'
        have htmp :
            (a.extract n a.size)[i - n] = a[n + (i - n)] := by
          exact
            (ByteArray.get_extract (a := a) (start := n) (stop := a.size)
              (i := i - n) hright)
        calc
          (a.extract n a.size)[i - n] = a[n + (i - n)] := htmp
          _ = a[i] := by
            simp [Nat.add_sub_of_le hge]
      calc
        (a.extract 0 n ++ a.extract n a.size)[i] =
            (a.extract n a.size)[i - n] := hget_right
        _ = a[i] := hget_extract

-- Copying a slice preserves the prefix before the destination offset.
lemma byteArray_copySlice_extract_prefix (src dest : ByteArray)
    (srcOff destOff len : Nat) (hdest : destOff + len ≤ dest.size) :
    (src.copySlice srcOff dest destOff len).extract 0 destOff = dest.extract 0 destOff := by
  have hdo : destOff ≤ dest.size := by omega
  have hsize : (dest.extract 0 destOff).size = destOff := by
    simp [ByteArray.size_extract, Nat.min_eq_left hdo]
  calc
    (src.copySlice srcOff dest destOff len).extract 0 destOff
        = (dest.extract 0 destOff ++
            src.extract srcOff (srcOff + len) ++
            dest.extract (destOff + min len (src.data.size - srcOff)) dest.data.size).extract 0 destOff := by
            simp [ByteArray.copySlice_eq_append, ByteArray.append_assoc]
    _ = (dest.extract 0 destOff).extract 0 destOff := by
          have hprefix :=
            byteArray_extract_append_prefix
              (a := dest.extract 0 destOff)
              (b := src.extract srcOff (srcOff + len) ++
                    dest.extract (destOff + min len (src.data.size - srcOff)) dest.data.size)
              (n := destOff) (by simp [hsize])
          simpa [ByteArray.append_assoc] using hprefix
    _ = dest.extract 0 destOff := by
          have hzero :
              (dest.extract 0 destOff).extract 0 (dest.extract 0 destOff).size =
                dest.extract 0 destOff := by
            simpa using (ByteArray.extract_zero_size (b := dest.extract 0 destOff))
          simpa [hsize] using hzero

-- Copying a slice installs the source segment at the destination offset.
lemma byteArray_copySlice_extract_mid (src dest : ByteArray)
    (srcOff destOff len : Nat) (hsrc : srcOff + len ≤ src.size) (hdest : destOff + len ≤ dest.size) :
    (src.copySlice srcOff dest destOff len).extract destOff (destOff + len) =
      src.extract srcOff (srcOff + len) := by
  have hmin : min len (src.size - srcOff) = len := by
    have hle : len ≤ src.size - srcOff := by
      have hsrc' : len + srcOff ≤ src.size := by
        simpa [Nat.add_comm] using hsrc
      exact Nat.le_sub_of_add_le hsrc'
    exact Nat.min_eq_left hle
  have hdo : destOff ≤ dest.size := by omega
  have hsize : (dest.extract 0 destOff).size = destOff := by
    simp [ByteArray.size_extract, Nat.min_eq_left hdo]
  have hmidSize : (src.extract srcOff (srcOff + len)).size = len := by
    simp [ByteArray.size_extract, Nat.min_eq_left hsrc]
  calc
    (src.copySlice srcOff dest destOff len).extract destOff (destOff + len)
        = (dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
            dest.extract (destOff + len) dest.size).extract destOff (destOff + len) := by
            simp [ByteArray.copySlice_eq_append, hmin, ByteArray.append_assoc, ByteArray.size_data]
    _ = (dest.extract 0 destOff ++
          (src.extract srcOff (srcOff + len) ++ dest.extract (destOff + len) dest.size)).extract
          destOff (destOff + len) := by
          simp [ByteArray.append_assoc]
    _ = (src.extract srcOff (srcOff + len) ++ dest.extract (destOff + len) dest.size).extract 0 len := by
          have h :=
            (ByteArray.extract_append_size_add'
              (a := dest.extract 0 destOff)
              (b := src.extract srcOff (srcOff + len) ++ dest.extract (destOff + len) dest.size)
              (i := 0) (j := len) (h := hsize.symm))
          simpa using h
    _ = (src.extract srcOff (srcOff + len)).extract 0 len := by
          have hprefix :=
            byteArray_extract_append_prefix
              (a := src.extract srcOff (srcOff + len))
              (b := dest.extract (destOff + len) dest.size)
              (n := len) (by simp [hmidSize])
          simpa using hprefix
    _ = src.extract srcOff (srcOff + len) := by
          have hzero :
              (src.extract srcOff (srcOff + len)).extract 0
                  (src.extract srcOff (srcOff + len)).size =
                src.extract srcOff (srcOff + len) := by
            simpa using
              (ByteArray.extract_zero_size (b := src.extract srcOff (srcOff + len)))
          simpa [hmidSize] using hzero

-- Copying a slice within bounds preserves the destination size.
lemma byteArray_copySlice_size (src dest : ByteArray)
    (srcOff destOff len : Nat) (hsrc : srcOff + len ≤ src.size) (hdest : destOff + len ≤ dest.size) :
    (src.copySlice srcOff dest destOff len).size = dest.size := by
  have hmin : min len (src.size - srcOff) = len := by
    have hle : len ≤ src.size - srcOff := by
      have hsrc' : len + srcOff ≤ src.size := by
        simpa [Nat.add_comm] using hsrc
      exact Nat.le_sub_of_add_le hsrc'
    exact Nat.min_eq_left hle
  have hdo : destOff ≤ dest.size := by omega
  calc
    (src.copySlice srcOff dest destOff len).size
        = (dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
            dest.extract (destOff + len) dest.size).size := by
            simp [ByteArray.copySlice_eq_append, hmin, ByteArray.append_assoc, ByteArray.size_data]
    _ = (dest.extract 0 destOff).size +
        (src.extract srcOff (srcOff + len)).size +
        (dest.extract (destOff + len) dest.size).size := by
          simp [ByteArray.size_append]
    _ = destOff + len + (dest.size - (destOff + len)) := by
          simp [ByteArray.size_extract, Nat.min_eq_left hdo, Nat.min_eq_left hsrc]
    _ = dest.size := by omega

-- Copying a slice preserves any prefix that ends before the destination offset.
lemma byteArray_copySlice_extract_prefix_le (src dest : ByteArray)
    (srcOff destOff len n : Nat) (hn : n ≤ destOff) (hdest : destOff + len ≤ dest.size) :
    (src.copySlice srcOff dest destOff len).extract 0 n = dest.extract 0 n := by
  have hprefix : (src.copySlice srcOff dest destOff len).extract 0 destOff = dest.extract 0 destOff := by
    exact byteArray_copySlice_extract_prefix (src := src) (dest := dest)
      (srcOff := srcOff) (destOff := destOff) (len := len) hdest
  have hleft :
      ((src.copySlice srcOff dest destOff len).extract 0 destOff).extract 0 n =
        (src.copySlice srcOff dest destOff len).extract 0 n := by
    simpa [Nat.min_eq_left hn] using
      (ByteArray.extract_extract
        (a := src.copySlice srcOff dest destOff len) (i := 0) (j := destOff) (k := 0) (l := n))
  have hright :
      (dest.extract 0 destOff).extract 0 n = dest.extract 0 n := by
    simpa [Nat.min_eq_left hn] using
      (ByteArray.extract_extract (a := dest) (i := 0) (j := destOff) (k := 0) (l := n))
  calc
    (src.copySlice srcOff dest destOff len).extract 0 n =
        ((src.copySlice srcOff dest destOff len).extract 0 destOff).extract 0 n := by
          simpa using hleft.symm
    _ = (dest.extract 0 destOff).extract 0 n := by
          simp [hprefix]
    _ = dest.extract 0 n := hright

-- If two byte arrays share a prefix, then any slice inside that prefix is equal.
lemma byteArray_extract_eq_of_prefix_eq (a b : ByteArray) (n i j : Nat)
    (hprefix : a.extract 0 n = b.extract 0 n) (hj : j ≤ n) :
    a.extract i j = b.extract i j := by
  have hleft :
      (a.extract 0 n).extract i j = a.extract i j := by
    simpa [Nat.min_eq_left hj] using
      (ByteArray.extract_extract (a := a) (i := 0) (j := n) (k := i) (l := j))
  have hright :
      (b.extract 0 n).extract i j = b.extract i j := by
    simpa [Nat.min_eq_left hj] using
      (ByteArray.extract_extract (a := b) (i := 0) (j := n) (k := i) (l := j))
  calc
    a.extract i j = (a.extract 0 n).extract i j := by
      simpa using hleft.symm
    _ = (b.extract 0 n).extract i j := by
      simp [hprefix]
    _ = b.extract i j := hright

-- Reading the single-byte extract recovers the original byte.
lemma byteArray_get!_eq_get (a : ByteArray) (i : Nat) (h : i < a.size) :
    a.get! i = a[i]'h := by
  cases a with
  | mk arr =>
      have h' : i < arr.size := by
        simpa using h
      calc
        arr[i]! = arr[i]'h' := by
          simp [getElem!_pos, h']
        _ = arr[i] := rfl

lemma byteArray_get!_extract0 (a : ByteArray) (start : Nat) (h : start + 1 ≤ a.size) :
    (a.extract start (start + 1)).get! 0 = a.get! start := by
  have hlt : start < a.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self start) h
  have hpos : 0 < (a.extract start (start + 1)).size := by
    simp [ByteArray.size_extract, Nat.min_eq_left h]
  have hget :
      (a.extract start (start + 1))[0]'hpos = a[start]'hlt := by
    simp [ByteArray.get_extract]
  calc
    (a.extract start (start + 1)).get! 0 =
        (a.extract start (start + 1))[0]'hpos := by
          simpa using (byteArray_get!_eq_get (a := a.extract start (start + 1)) (i := 0) hpos)
    _ = a[start]'hlt := hget
    _ = a.get! start := by
          simpa using (byteArray_get!_eq_get (a := a) (i := start) hlt).symm

-- Extending a prefix equality by matching the next slice.
lemma byteArray_extract_prefix_extend (a b : ByteArray) (n m : Nat)
    (hnm : n ≤ m) (ha : m ≤ a.size) (hb : m ≤ b.size)
    (hprefix : a.extract 0 n = b.extract 0 n)
    (hmid : a.extract n m = b.extract n m) :
    a.extract 0 m = b.extract 0 m := by
  have hsize_a : (a.extract 0 m).size = m := by
    simp [ByteArray.size_extract, Nat.min_eq_left ha]
  have hsize_b : (b.extract 0 m).size = m := by
    simp [ByteArray.size_extract, Nat.min_eq_left hb]
  have hn_a : n ≤ (a.extract 0 m).size := by
    simpa [hsize_a] using hnm
  have hn_b : n ≤ (b.extract 0 m).size := by
    simpa [hsize_b] using hnm
  have hsplit_a :
      a.extract 0 m = a.extract 0 n ++ a.extract n m := by
    have hsplit := byteArray_extract_split (a := a.extract 0 m) (n := n) (hn := hn_a)
    have hleft :
        (a.extract 0 m).extract 0 n = a.extract 0 n := by
      simpa [Nat.min_eq_left hnm] using
        (ByteArray.extract_extract (a := a) (i := 0) (j := m) (k := 0) (l := n))
    have hright :
        (a.extract 0 m).extract n m = a.extract n m := by
      simpa [Nat.min_eq_left (le_rfl : m ≤ m)] using
        (ByteArray.extract_extract (a := a) (i := 0) (j := m) (k := n) (l := m))
    calc
      a.extract 0 m =
          (a.extract 0 m).extract 0 n ++ (a.extract 0 m).extract n (a.extract 0 m).size := by
            simpa [hsize_a] using hsplit.symm
      _ = (a.extract 0 m).extract 0 n ++ (a.extract 0 m).extract n m := by
            simp [hsize_a]
      _ = a.extract 0 n ++ a.extract n m := by
            simp [hleft, hright]
  have hsplit_b :
      b.extract 0 m = b.extract 0 n ++ b.extract n m := by
    have hsplit := byteArray_extract_split (a := b.extract 0 m) (n := n) (hn := hn_b)
    have hleft :
        (b.extract 0 m).extract 0 n = b.extract 0 n := by
      simpa [Nat.min_eq_left hnm] using
        (ByteArray.extract_extract (a := b) (i := 0) (j := m) (k := 0) (l := n))
    have hright :
        (b.extract 0 m).extract n m = b.extract n m := by
      simpa [Nat.min_eq_left (le_rfl : m ≤ m)] using
        (ByteArray.extract_extract (a := b) (i := 0) (j := m) (k := n) (l := m))
    calc
      b.extract 0 m =
          (b.extract 0 m).extract 0 n ++ (b.extract 0 m).extract n (b.extract 0 m).size := by
            simpa [hsize_b] using hsplit.symm
      _ = (b.extract 0 m).extract 0 n ++ (b.extract 0 m).extract n m := by
            simp [hsize_b]
      _ = b.extract 0 n ++ b.extract n m := by
            simp [hleft, hright]
  calc
    a.extract 0 m = a.extract 0 n ++ a.extract n m := hsplit_a
    _ = b.extract 0 n ++ b.extract n m := by
          simp [hprefix, hmid]
    _ = b.extract 0 m := hsplit_b.symm

-- Copying a slice does not affect bytes beyond the destination range.
lemma byteArray_copySlice_get_of_ge (src dest : ByteArray)
    (srcOff destOff len i : Nat) (hsrc : srcOff + len ≤ src.size)
    (hdest : destOff + len ≤ dest.size) (hi : destOff + len ≤ i) (hi' : i < dest.size) :
    (src.copySlice srcOff dest destOff len)[i]'(by
        have hsize :=
          byteArray_copySlice_size (src := src) (dest := dest)
            (srcOff := srcOff) (destOff := destOff) (len := len) hsrc hdest
        simpa [hsize] using hi') = dest[i]'hi' := by
  have hmin : min len (src.size - srcOff) = len := by
    have hle : len ≤ src.size - srcOff := by
      have hsrc' : len + srcOff ≤ src.size := by
        simpa [Nat.add_comm] using hsrc
      exact Nat.le_sub_of_add_le hsrc'
    exact Nat.min_eq_left hle
  let left :=
    dest.extract 0 destOff ++ src.extract srcOff (srcOff + len)
  let right := dest.extract (destOff + len) dest.size
  have hsize_left : left.size = destOff + len := by
    have hdo : destOff ≤ dest.size := by omega
    have hsize_dest : (dest.extract 0 destOff).size = destOff := by
      simp [ByteArray.size_extract, Nat.min_eq_left hdo]
    have hsize_src : (src.extract srcOff (srcOff + len)).size = len := by
      simp [ByteArray.size_extract, Nat.min_eq_left hsrc]
    simp [left, ByteArray.size_append, hsize_dest, hsize_src]
  have hsize_copy : (src.copySlice srcOff dest destOff len).size = dest.size := by
    exact
      byteArray_copySlice_size (src := src) (dest := dest)
        (srcOff := srcOff) (destOff := destOff) (len := len) hsrc hdest
  have hsize_right : right.size = dest.size - (destOff + len) := by
    have hdo : destOff + len ≤ dest.size := hdest
    simp [right, ByteArray.size_extract]
  have hsize_lr : (left ++ right).size = dest.size := by
    simp [ByteArray.size_append, hsize_left, hsize_right, Nat.add_sub_of_le hdest]
  have hi'' : i < (left ++ right).size := by
    simpa [hsize_lr] using hi'
  have hle : left.size ≤ i := by
    simpa [hsize_left] using hi
  have hget :=
    (ByteArray.get_append_right (a := left) (b := right) (i := i) (hle := hle) (h := hi''))
  have hidx' : i - left.size < right.size := by
    have hsub : i - (destOff + len) < dest.size - (destOff + len) := by
      exact Nat.sub_lt_sub_right (by simpa [hsize_left] using hle) hi'
    simpa [hsize_left, hsize_right] using hsub
  have hcalc : i - left.size = i - (destOff + len) := by
    simp [hsize_left]
  have hidx'' : i - (destOff + len) < right.size := by
    simpa [hcalc] using hidx'
  have hget' :=
    (ByteArray.get_extract (a := dest) (start := destOff + len) (stop := dest.size)
      (i := i - (destOff + len)) (by
        simpa [hsize_right] using hidx''))
  calc
    (src.copySlice srcOff dest destOff len)[i]'(by
        have hsize :=
          byteArray_copySlice_size (src := src) (dest := dest)
            (srcOff := srcOff) (destOff := destOff) (len := len) hsrc hdest
        simpa [hsize] using hi')
        = (left ++ right)[i]'hi'' := by
            simp [left, right, ByteArray.copySlice_eq_append, hmin, ByteArray.append_assoc, ByteArray.size_data]
    _ = right[i - left.size]'hidx' := by
          simpa using hget
    _ = dest[i]'hi' := by
          simp [right, hcalc, Nat.add_sub_of_le hi, hget']


def BitWriter.bitCount (bw : BitWriter) : Nat :=
  bw.out.size * 8 + bw.bitPos

@[simp] lemma bitCount_empty : BitWriter.bitCount BitWriter.empty = 0 := by
  simp [BitWriter.bitCount, BitWriter.empty]

lemma bitCount_writeBit (bw : BitWriter) (bit : Nat) :
    (BitWriter.writeBit bw bit).bitCount = bw.bitCount + 1 := by
  unfold BitWriter.writeBit BitWriter.bitCount
  by_cases h : bw.bitPos = 7
  · simp [h]
    omega
  · simp [h]
    omega

lemma bitCount_writeBits (bw : BitWriter) (bits len : Nat) :
    (BitWriter.writeBits bw bits len).bitCount = bw.bitCount + len := by
  induction len generalizing bw bits with
  | zero =>
      simp [BitWriter.writeBits]
  | succ n ih =>
      simp [BitWriter.writeBits, ih, bitCount_writeBit, Nat.add_assoc, Nat.add_comm]

lemma flush_size (bw : BitWriter) :
    bw.flush.size = bw.out.size + (if bw.bitPos = 0 then 0 else 1) := by
  by_cases h : bw.bitPos = 0 <;> simp [BitWriter.flush, h]

lemma flush_size_mul_ge_bitCount (bw : BitWriter) (hbit : (bw.bitPos < 8)) :
    bw.flush.size * 8 ≥ bw.bitCount := by
  unfold BitWriter.bitCount
  by_cases h : bw.bitPos = 0
  · simp [flush_size, h, Nat.add_comm]
  · have hsize : bw.flush.size = bw.out.size + 1 := by
      simp [flush_size, h]
    calc
      bw.flush.size * 8 = (bw.out.size + 1) * 8 := by
        simp [hsize]
      _ = bw.out.size * 8 + 8 := by
        omega
      _ ≥ bw.out.size * 8 + bw.bitPos := by
        omega

-- Writing a bit keeps the bit position in range.
lemma bitPos_lt_8_writeBit (bw : BitWriter) (bit : Nat) (_hbit : (bw.bitPos < 8)) :
    ((BitWriter.writeBit bw bit).bitPos) < 8 := by
  simpa using (BitWriter.writeBit bw bit).hbit

-- Writing multiple bits keeps the bit position in range.
lemma bitPos_lt_8_writeBits (bw : BitWriter) (bits len : Nat) (_hbit : (bw.bitPos < 8)) :
    ((BitWriter.writeBits bw bits len).bitPos) < 8 := by
  simpa using (BitWriter.writeBits bw bits len).hbit

-- Writing a bit does not shrink the output buffer.
lemma out_size_writeBit_le (bw : BitWriter) (bit : Nat) :
    bw.out.size ≤ (BitWriter.writeBit bw bit).out.size := by
  unfold BitWriter.writeBit
  by_cases h : bw.bitPos = 7 <;> simp [h, Nat.le_succ]

-- Writing bits does not shrink the output buffer.
lemma out_size_writeBits_le (bw : BitWriter) (bits len : Nat) :
    bw.out.size ≤ (BitWriter.writeBits bw bits len).out.size := by
  induction len generalizing bw bits with
  | zero =>
      simp [BitWriter.writeBits]
  | succ n ih =>
      have hle := out_size_writeBit_le bw (bits % 2)
      have hle' := ih (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1)
      have htrans : bw.out.size ≤ (BitWriter.writeBit bw (bits % 2)).out.size :=
        hle
      exact le_trans htrans hle'

-- Flush never shrinks the output.
lemma out_size_le_flush (bw : BitWriter) : bw.out.size ≤ bw.flush.size := by
  by_cases h : bw.bitPos = 0 <;> simp [BitWriter.flush, h]

-- Writing one bit always extends the flushed buffer by exactly one byte.
lemma flush_size_writeBit (bw : BitWriter) (bit : Nat) :
    (BitWriter.writeBit bw bit).flush.size = bw.out.size + 1 := by
  by_cases h : bw.bitPos = 7 <;> simp [BitWriter.writeBit, BitWriter.flush, h]

-- Writing one bit never shrinks the flushed buffer.
lemma flush_size_writeBit_le (bw : BitWriter) (bit : Nat) :
    bw.flush.size ≤ (BitWriter.writeBit bw bit).flush.size := by
  have h1 : (BitWriter.writeBit bw bit).flush.size = bw.out.size + 1 :=
    flush_size_writeBit bw bit
  by_cases h0 : bw.bitPos = 0
  · simp [flush_size, h0, h1]
  · simp [flush_size, h0, h1]

-- Writing bits never shrinks the flushed buffer.
lemma flush_size_writeBits_le (bw : BitWriter) (bits len : Nat) :
    bw.flush.size ≤ (BitWriter.writeBits bw bits len).flush.size := by
  induction len generalizing bw bits with
  | zero =>
      simp [BitWriter.writeBits]
  | succ n ih =>
      have h1 : bw.flush.size ≤ (BitWriter.writeBit bw (bits % 2)).flush.size := by
        have hle : bw.flush.size ≤ bw.out.size + 1 := by
          by_cases h0 : bw.bitPos = 0 <;> simp [BitWriter.flush, h0]
        -- rewrite the right-hand side using the exact flush size
        simpa [flush_size_writeBit] using hle
      have h2 :=
        ih (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1)
      exact le_trans h1 h2

-- Writing at least one bit strictly grows the flushed buffer.
lemma flush_size_writeBits_lt (bw : BitWriter) (bits len : Nat) (h : 0 < len) :
    bw.out.size < (BitWriter.writeBits bw bits len).flush.size := by
  cases len with
  | zero => cases h
  | succ n =>
      have h1 : (BitWriter.writeBit bw (bits % 2)).flush.size = bw.out.size + 1 :=
        flush_size_writeBit bw (bits % 2)
      have hle :
          (BitWriter.writeBit bw (bits % 2)).flush.size ≤
            (BitWriter.writeBits bw bits (Nat.succ n)).flush.size := by
        -- unfold one step, then use monotonicity
        simpa [BitWriter.writeBits] using
          (flush_size_writeBits_le (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1) (len := n))
      calc
        bw.out.size < bw.out.size + 1 := by omega
        _ = (BitWriter.writeBit bw (bits % 2)).flush.size := by simp [h1]
        _ ≤ (BitWriter.writeBits bw bits (Nat.succ n)).flush.size := hle

-- Bits at and above the current position are clear in the working byte.
def BitWriter.curClearAbove (bw : BitWriter) : Prop :=
  ∀ i, bw.bitPos ≤ i → i < 8 → bw.cur.toNat.testBit i = false

lemma curClearAbove_empty : BitWriter.curClearAbove BitWriter.empty := by
  intro i _ hlt
  simp [BitWriter.empty]

lemma curClearAbove_writeBit (bw : BitWriter) (bit : Nat) (hbit : (bw.bitPos < 8))
    (hcur : bw.curClearAbove) :
    (BitWriter.writeBit bw bit).curClearAbove := by
  intro i hi hlt
  unfold BitWriter.writeBit
  by_cases h : bw.bitPos = 7
  · simp [h]
  · -- i ≥ bitPos + 1, so the new bit does not affect position i.
    have hpos : bw.bitPos + 1 ≤ i := by
      simpa [BitWriter.writeBit, h] using hi
    have hpos' : bw.bitPos < i := lt_of_lt_of_le (Nat.lt_succ_self _) hpos
    have hle : bw.bitPos ≤ i := Nat.le_of_lt hpos'
    have hlt' : bw.bitPos < 8 := hbit
    have hshift_lt : (bit % 2) <<< bw.bitPos < 2 ^ 8 := by
      have hbit' : bit % 2 < 2 := by
        exact Nat.mod_lt _ (by decide : 0 < 2)
      have hbit'' : bit % 2 ≤ 1 := Nat.lt_succ_iff.mp hbit'
      have hpow : 2 ^ bw.bitPos ≤ 2 ^ 7 := by
        have hle' : bw.bitPos ≤ 7 := Nat.le_of_lt_succ hbit
        exact Nat.pow_le_pow_of_le (by decide : 1 < 2) hle'
      have : (bit % 2) <<< bw.bitPos ≤ 1 * 2 ^ bw.bitPos := by
        simpa [Nat.shiftLeft_eq] using Nat.mul_le_mul_right (2 ^ bw.bitPos) hbit''
      have : (bit % 2) <<< bw.bitPos ≤ 2 ^ 7 := by
        exact le_trans this (by simpa [Nat.mul_one] using hpow)
      have : (bit % 2) <<< bw.bitPos < 2 ^ 8 := by
        exact lt_of_le_of_lt this (by decide : 2 ^ 7 < 2 ^ 8)
      exact this
    have hcur' : bw.cur.toNat.testBit i = false := hcur i hle hlt
    have hbitpos : (((bit % 2) <<< bw.bitPos) % 256).testBit i = false := by
      have htest :
          (((bit % 2) <<< bw.bitPos).testBit i) = false := by
        -- Use the shift-left testBit lemma.
        have hle' : bw.bitPos ≤ i := Nat.le_of_lt hpos'
        have hshift :
            (((bit % 2) <<< bw.bitPos).testBit i) =
              (decide (i ≥ bw.bitPos) && (bit % 2).testBit (i - bw.bitPos)) := by
          simp [Nat.testBit_shiftLeft]
        -- Since i > bw.bitPos, the decide is true.
        have hsrc : 1 ≤ i - bw.bitPos := by
          -- from bw.bitPos + 1 ≤ i
          exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hpos)
        have hsmall : bit % 2 < 2 ^ 1 := by
          exact Nat.mod_lt _ (by decide : 0 < 2)
        have hzero : (bit % 2).testBit (i - bw.bitPos) = false := by
          apply Nat.testBit_lt_two_pow
          have hle'' : 2 ^ 1 ≤ 2 ^ (i - bw.bitPos) := by
            exact Nat.pow_le_pow_of_le (by decide : 1 < 2) hsrc
          exact lt_of_lt_of_le hsmall hle''
        -- simplify the shift-left formula
        have hdec : decide (i ≥ bw.bitPos) = true := by
          exact decide_eq_true hle'
        -- now finish
        simp [hshift, hdec, hzero]
      have hmod : ((bit % 2) <<< bw.bitPos) % 256 = (bit % 2) <<< bw.bitPos :=
        Nat.mod_eq_of_lt hshift_lt
      -- rewrite the modulus and use the plain shift-left result
      rw [hmod]
      exact htest
    -- Combine both parts of the OR.
    have hcurNat :
        (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat.testBit i = false := by
      -- Convert to Nat and use testBit_or.
      calc
        (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat.testBit i
            =
            (bw.cur.toNat ||| (((bit % 2) <<< bw.bitPos) % 256)).testBit i := by
              simp [UInt8.toNat_or, -UInt8.ofNat_shiftLeft]
        _ = (bw.cur.toNat.testBit i ||
              (((bit % 2) <<< bw.bitPos) % 256).testBit i) := by
              simp [Nat.testBit_or]
        _ = false := by
              simp [hcur', hbitpos]
    simpa [BitWriter.curClearAbove, BitWriter.writeBit, h] using hcurNat

lemma curClearAbove_writeBits (bw : BitWriter) (bits len : Nat) (hbit : (bw.bitPos < 8))
    (hcur : bw.curClearAbove) :
    (BitWriter.writeBits bw bits len).curClearAbove := by
  induction len generalizing bw bits with
  | zero =>
      simp [BitWriter.writeBits, hcur]
  | succ n ih =>
      have hcur' := curClearAbove_writeBit bw (bits % 2) hbit hcur
      have hbit' : (BitWriter.writeBit bw (bits % 2)).bitPos < 8 :=
        bitPos_lt_8_writeBit bw (bits % 2) hbit
      simpa [BitWriter.writeBits] using
        (ih (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1) hbit' hcur')

-- Build a bit reader at the current writer position.
def BitWriter.toReader (bw : BitWriter) (hbit : (bw.bitPos < 8)) : BitReader :=
  { data := bw.flush
    bytePos := bw.out.size
    bitPos := bw.bitPos
    hpos := out_size_le_flush bw
    hend := by
      intro hEq
      by_cases h0 : (bw.bitPos = 0)
      · exact h0
      · exfalso
        have hsize : bw.flush.size = bw.out.size + 1 := by
          simp [BitWriter.flush, h0]
        have hlt : bw.out.size < bw.flush.size := by
          simp [hsize]
        exact (Nat.ne_of_lt hlt) hEq
    hbit := hbit }

@[simp] lemma bitIndex_toReader (bw : BitWriter) (hbit : (bw.bitPos < 8)) :
    (BitWriter.toReader bw hbit).bitIndex = bw.bitCount := by
  simp [BitWriter.toReader, BitReader.bitIndex, BitWriter.bitCount]

-- Build a reader at the current writer position over an external buffer.
def BitWriter.readerAt (bw : BitWriter) (data : ByteArray)
    (hflush : bw.flush.size ≤ data.size) (hbit : (bw.bitPos < 8)) : BitReader :=
  { data := data
    bytePos := bw.out.size
    bitPos := bw.bitPos
    hpos := le_trans (out_size_le_flush bw) hflush
    hend := by
      intro hEq
      by_cases h0 : (bw.bitPos = 0)
      · exact h0
      · exfalso
        have hsize : bw.flush.size = bw.out.size + 1 := by
          simp [BitWriter.flush, h0]
        have hlt : bw.out.size < bw.flush.size := by
          simp [hsize]
        have hlt' : bw.out.size < data.size := lt_of_lt_of_le hlt hflush
        exact (Nat.ne_of_lt hlt') hEq
    hbit := hbit }

@[simp] lemma bitIndex_readerAt (bw : BitWriter) (data : ByteArray)
    (hflush : bw.flush.size ≤ data.size) (hbit : (bw.bitPos < 8)) :
    (BitWriter.readerAt bw data hflush hbit).bitIndex = bw.bitCount := by
  simp [BitWriter.readerAt, BitReader.bitIndex, BitWriter.bitCount]

-- Aligning a reader at the writer position reaches the flush size.
lemma readerAt_alignByte_bytePos_eq_flush (bw : BitWriter) (hbit : bw.bitPos < 8) :
    (BitWriter.readerAt bw bw.flush (by rfl) hbit).alignByte.bytePos = bw.flush.size := by
  by_cases h0 : bw.bitPos = 0
  · simp [BitWriter.readerAt, BitReader.alignByte, BitWriter.flush, h0]
  · have hsize : bw.flush.size = bw.out.size + 1 := by
      simp [BitWriter.flush, h0]
    simp [BitWriter.readerAt, BitReader.alignByte, h0, hsize]

-- Aligning with an explicit data buffer equal to the flush.
lemma readerAt_alignByte_bytePos_eq_data (bw : BitWriter) (data : ByteArray)
    (hflush : bw.flush.size ≤ data.size) (hbit : bw.bitPos < 8) (hdata : data = bw.flush) :
    (BitWriter.readerAt bw data hflush hbit).alignByte.bytePos = data.size := by
  subst hdata
  simpa using (readerAt_alignByte_bytePos_eq_flush (bw := bw) hbit)


-- Convert a bit read to a testBit value.
lemma bitNat_of_testBit (x i : Nat) :
    ((x >>> i) &&& 1) = (x.testBit i).toNat := by
  calc
    (x >>> i) &&& 1 = (x >>> i) % 2 := by
      simp [Nat.and_one_is_mod]
    _ = x / 2 ^ i % 2 := by
      simp [Nat.shiftRight_eq_div_pow]
    _ = (x.testBit i).toNat := by
      symm
      simpa using (Nat.toNat_testBit x i)

-- Flush after writing one bit is the current output plus the updated byte.
lemma writeBit_flush_eq (bw : BitWriter) (bit : Nat) :
    (BitWriter.writeBit bw bit).flush =
      bw.out.push (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) := by
  by_cases h7 : bw.bitPos = 7 <;> simp [BitWriter.writeBit, BitWriter.flush, h7]

-- The extracted bit from the updated current byte is the written bit.
lemma bitNat_writeBit (bw : BitWriter) (bit : Nat)
    (hbit : (bw.bitPos < 8)) (hcur : bw.curClearAbove) :
    ((bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat >>> bw.bitPos) &&& 1 =
      bit % 2 := by
  have hcur0 : bw.cur.toNat.testBit bw.bitPos = false :=
    hcur bw.bitPos (le_rfl) hbit
  have hmod : bit % 2 = 0 ∨ bit % 2 = 1 := Nat.mod_two_eq_zero_or_one bit
  cases hmod with
  | inl h0 =>
      -- bit % 2 = 0
      calc
        ((bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat >>> bw.bitPos) &&& 1
            = ((bw.cur ||| UInt8.ofNat (0 <<< bw.bitPos)).toNat >>> bw.bitPos) &&& 1 := by
                simp [h0]
        _ = ((bw.cur ||| (0 : UInt8)).toNat >>> bw.bitPos) &&& 1 := by
                simp
        _ = (bw.cur.toNat >>> bw.bitPos) &&& 1 := by
                simp
        _ = (bw.cur.toNat.testBit bw.bitPos).toNat := by
                simpa using (bitNat_of_testBit (x := bw.cur.toNat) (i := bw.bitPos))
        _ = 0 := by
                simp [hcur0]
        _ = bit % 2 := by
                simp [h0]
  | inr h1 =>
      -- bit % 2 = 1
      have hshift_lt : (1 <<< bw.bitPos) < 2 ^ 8 := by
        have hpow : 2 ^ bw.bitPos ≤ 2 ^ 7 := by
          have hle' : bw.bitPos ≤ 7 := Nat.le_of_lt_succ hbit
          exact Nat.pow_le_pow_of_le (by decide : 1 < 2) hle'
        have hle : (1 <<< bw.bitPos) ≤ 2 ^ 7 := by
          simpa [Nat.shiftLeft_eq, Nat.mul_one] using hpow
        exact lt_of_le_of_lt hle (by decide : 2 ^ 7 < 2 ^ 8)
      have hmod1 : (1 <<< bw.bitPos) % 256 = 1 <<< bw.bitPos := by
        have hlt : (1 <<< bw.bitPos) < 256 := by
          simpa using hshift_lt
        exact Nat.mod_eq_of_lt hlt
      have hsub : bw.bitPos - bw.bitPos = 0 := by omega
      have htest_shift : ((1 <<< bw.bitPos).testBit bw.bitPos) = true := by
        simp [Nat.testBit_shiftLeft]
      have htest_shift_mod : ((1 <<< bw.bitPos % 256).testBit bw.bitPos) = true := by
        simp [hmod1, htest_shift]
      have htest_or :
          ((bw.cur ||| UInt8.ofNat (1 <<< bw.bitPos)).toNat.testBit bw.bitPos) = true := by
        have htest_or'' :
            ((bw.cur ||| UInt8.ofNat (1 <<< bw.bitPos)).toNat.testBit bw.bitPos) =
              (bw.cur.toNat.testBit bw.bitPos ||
                (1 <<< bw.bitPos % 256).testBit bw.bitPos) := by
          simp [UInt8.toNat_or, -UInt8.ofNat_shiftLeft]
        have hbool :
            (bw.cur.toNat.testBit bw.bitPos ||
              (1 <<< bw.bitPos % 256).testBit bw.bitPos) = true := by
          have h :
              bw.cur.toNat.testBit bw.bitPos = true ∨
                (1 <<< bw.bitPos % 256).testBit bw.bitPos = true := by
            exact Or.inr htest_shift_mod
          simpa [Bool.or_eq_true] using h
        exact htest_or''.trans hbool
      calc
        ((bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat >>> bw.bitPos) &&& 1
            = ((bw.cur ||| UInt8.ofNat (1 <<< bw.bitPos)).toNat >>> bw.bitPos) &&& 1 := by
                simp [h1]
        _ = ((bw.cur ||| UInt8.ofNat (1 <<< bw.bitPos)).toNat.testBit bw.bitPos).toNat := by
                simpa using (bitNat_of_testBit
                  (x := (bw.cur ||| UInt8.ofNat (1 <<< bw.bitPos)).toNat)
                  (i := bw.bitPos))
        _ = 1 := by
                rw [htest_or]
                simp
        _ = bit % 2 := by
                simp [h1]


-- Extensionality for BitReader ignoring proof fields.
theorem BitReader.ext {br1 br2 : BitReader}
    (hdata : br1.data = br2.data) (hbyte : br1.bytePos = br2.bytePos)
    (hbit : br1.bitPos = br2.bitPos) : br1 = br2 := by
  cases br1
  cases br2
  cases hdata
  cases hbyte
  cases hbit
  -- proof fields are propositions, so they are proof-irrelevant
  simp

-- Reading the next bit from a writer-aligned reader returns the last written bit.
lemma readBit_readerAt_writeBit (bw : BitWriter) (bit : Nat)
    (hbit : (bw.bitPos < 8)) (hcur : bw.curClearAbove) :
    let bw' := BitWriter.writeBit bw bit
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBit_le bw bit) hbit
    br.readBit =
      (bit % 2,
        BitWriter.readerAt bw' bw'.flush (by rfl) (bitPos_lt_8_writeBit bw bit hbit)) := by
  classical
  -- unfold the lets
  dsimp
  by_cases h7 : bw.bitPos = 7
  · -- reader advances to next byte
    have h7nat : bw.bitPos = 7 := h7
    have hnext : bw.bitPos + 1 = 8 := by
      omega
    have hlt : bw.out.size < (BitWriter.writeBit bw bit).flush.size := by
      simp [flush_size_writeBit]
    have hne : bw.out.size ≠ (BitWriter.writeBit bw bit).flush.size :=
      ne_of_lt hlt
    have hbyte' :
        (BitWriter.writeBit bw bit).flush[bw.out.size]'hlt =
          (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) := by
      simp [writeBit_flush_eq, ByteArray.get_push_eq]
    have hbyte :
        (BitWriter.writeBit bw bit).flush.get bw.out.size hlt =
          (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) := by
      simp [byteArray_get_eq_getElem, hbyte']
    -- evaluate readBit
    have hread :
        (BitWriter.readerAt bw (BitWriter.writeBit bw bit).flush (flush_size_writeBit_le bw bit) hbit).readBit
          = (bit % 2,
              { data := (BitWriter.writeBit bw bit).flush
                bytePos := bw.out.size + 1
                bitPos := 0
                hpos := by
                  simp [flush_size_writeBit]
                hend := by intro _; rfl
                hbit := by decide }) := by
      have hbitnat := bitNat_writeBit bw bit hbit hcur
      -- reduce the reader; discharge the bit computation via `hbitnat`.
      simp [BitWriter.readerAt, BitReader.readBit, hne, hbyte, h7nat,
        -UInt8.toNat_or, -UInt8.ofNat_shiftLeft, -Nat.and_one_is_mod]
      simpa [h7nat] using hbitnat
    -- show the reader matches readerAt for bw'
    have hreader :
        ( { data := (BitWriter.writeBit bw bit).flush
            bytePos := bw.out.size + 1
            bitPos := 0
            hpos := by
              simp [flush_size_writeBit]
            hend := by intro _; rfl
            hbit := by decide } :
          BitReader)
          =
          BitWriter.readerAt (BitWriter.writeBit bw bit) (BitWriter.writeBit bw bit).flush (by rfl)
            (bitPos_lt_8_writeBit bw bit hbit) := by
      apply BitReader.ext <;> simp [BitWriter.readerAt, BitWriter.writeBit, h7]
    -- finish
    simp [hread, hreader]

  · -- reader stays in same byte
    have h7nat : bw.bitPos ≠ 7 := h7
    have hnext : bw.bitPos + 1 ≠ 8 := by
      omega
    have hlt : bw.out.size < (BitWriter.writeBit bw bit).flush.size := by
      simp [flush_size_writeBit]
    have hne : bw.out.size ≠ (BitWriter.writeBit bw bit).flush.size :=
      ne_of_lt hlt
    have hbyte' :
        (BitWriter.writeBit bw bit).flush[bw.out.size]'hlt =
          (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) := by
      simp [writeBit_flush_eq, ByteArray.get_push_eq]
    have hbyte :
        (BitWriter.writeBit bw bit).flush.get bw.out.size hlt =
          (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) := by
      simp [byteArray_get_eq_getElem, hbyte']
    have hread :
        (BitWriter.readerAt bw (BitWriter.writeBit bw bit).flush (flush_size_writeBit_le bw bit) hbit).readBit
          = (bit % 2,
              { data := (BitWriter.writeBit bw bit).flush
                bytePos := bw.out.size
                bitPos := bw.bitPos + 1
                hpos := by
                  have hpos' : bw.out.size ≤ (BitWriter.writeBit bw bit).flush.size := by
                    have hpos' : bw.out.size ≤ bw.flush.size := out_size_le_flush bw
                    exact le_trans hpos' (flush_size_writeBit_le bw bit)
                  simpa using hpos'
                hend := by
                  intro hEq
                  have hlt : bw.out.size < (BitWriter.writeBit bw bit).flush.size := by
                    simp [flush_size_writeBit]
                  exact (False.elim ((Nat.ne_of_lt hlt) hEq))
                hbit := by
                  have hlt : bw.bitPos < 7 := by
                    exact lt_of_le_of_ne (Nat.le_of_lt_succ hbit) h7
                  have hbit' : bw.bitPos + 1 < 8 := by
                    simpa [Nat.succ_eq_add_one] using (Nat.succ_lt_succ_iff.mpr hlt)
                  simpa [Nat.add_comm] using hbit' }) := by
      have hbitnat := bitNat_writeBit bw bit hbit hcur
      simp [BitWriter.readerAt, BitReader.readBit, hne, hbyte, hnext,
        -UInt8.toNat_or, -UInt8.ofNat_shiftLeft, -Nat.and_one_is_mod]
      simpa using hbitnat
    have hreader :
        ( { data := (BitWriter.writeBit bw bit).flush
            bytePos := bw.out.size
            bitPos := bw.bitPos + 1
            hpos := by
              have hpos' : bw.out.size ≤ (BitWriter.writeBit bw bit).flush.size := by
                have hpos' : bw.out.size ≤ bw.flush.size := out_size_le_flush bw
                exact le_trans hpos' (flush_size_writeBit_le bw bit)
              simpa using hpos'
            hend := by
              intro hEq
              have hlt : bw.out.size < (BitWriter.writeBit bw bit).flush.size := by
                simp [flush_size_writeBit]
              exact (False.elim ((Nat.ne_of_lt hlt) hEq))
            hbit := by
              have hlt : bw.bitPos < 7 := by
                exact lt_of_le_of_ne (Nat.le_of_lt_succ hbit) h7
              have hbit' : bw.bitPos + 1 < 8 := by
                simpa [Nat.succ_eq_add_one] using (Nat.succ_lt_succ_iff.mpr hlt)
              simpa [Nat.add_comm] using hbit' } : BitReader)
          =
          BitWriter.readerAt (BitWriter.writeBit bw bit) (BitWriter.writeBit bw bit).flush (by rfl)
            (bitPos_lt_8_writeBit bw bit hbit) := by
      apply BitReader.ext <;> simp [BitWriter.readerAt, BitWriter.writeBit, h7]
    simp [hread, hreader]

-- Decompose the low bits of a number into its LSB and the shifted remainder.
lemma mod_two_pow_decomp (bits n : Nat) :
    bits % 2 ^ (n + 1) =
      (bits % 2) ||| (((bits >>> 1) % 2 ^ n) <<< 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
      -- low bit comes from `bits % 2`; the shifted remainder has bit 0 cleared.
      simp
  | succ k =>
      -- higher bits come from the shifted remainder.
      have hbit0 : (bits % 2).testBit (k + 1) = false := by
        have hlt : ¬k + 1 < 1 := by omega
        have h := (Nat.testBit_mod_two_pow bits 1 (k + 1))
        simpa [hlt] using h
      by_cases hk : k < n
      · have hk' : k + 1 < n + 1 := Nat.succ_lt_succ hk
        simp [hk, hk', hbit0, Nat.add_comm]
      · have hk' : ¬k + 1 < n + 1 := by
          exact not_lt_of_ge (Nat.succ_le_succ (Nat.le_of_not_gt hk))
        simp [hk, hk', hbit0, Nat.add_comm]

-- Decompose a low `(n+1)`-bit window into the first `n` bits and the `n`-th bit.
lemma mod_two_pow_decomp_high (bits n : Nat) :
    bits % 2 ^ (n + 1) =
      (bits % 2 ^ n) ||| (((bits >>> n) % 2) <<< n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · -- lower bits come from the `n`-bit prefix
    have hshift : (((bits >>> n) % 2) <<< n).testBit i = false := by
      have hle : ¬ i ≥ n := Nat.not_le_of_gt hi
      simp [Nat.testBit_shiftLeft, hle]
    have hleft :
        (bits % 2 ^ n).testBit i = bits.testBit i := by
      simp [Nat.testBit_mod_two_pow, hi]
    have hlt' : i < n + 1 := lt_trans hi (Nat.lt_succ_self n)
    have hright :
        (bits % 2 ^ (n + 1)).testBit i = bits.testBit i := by
      simp [Nat.testBit_mod_two_pow, hlt']
    simp [Nat.testBit_or, hshift, hleft, hright]
  · have hge : n ≤ i := Nat.le_of_not_gt hi
    cases lt_or_eq_of_le hge with
    | inl hgt =>
        -- `i > n`: both sides are zero
        have hlt' : ¬ i < n + 1 := by omega
        have hleft :
            (bits % 2 ^ (n + 1)).testBit i = false := by
          simp [Nat.testBit_mod_two_pow, hlt']
        have hright1 :
            (bits % 2 ^ n).testBit i = false := by
          have hlt'' : ¬ i < n := by omega
          simp [Nat.testBit_mod_two_pow, hlt'']
        have hx : ((bits >>> n) % 2) < 2 := Nat.mod_lt _ (by decide : 0 < (2 : Nat))
        have hpos : 0 < i - n := by omega
        have hpow : 2 ≤ 2 ^ (i - n) := by
          have hle1 : 1 ≤ i - n := Nat.succ_le_of_lt hpos
          have := Nat.pow_le_pow_of_le (a := 2) (by decide) hle1
          simpa [Nat.pow_succ] using this
        have hltx : ((bits >>> n) % 2) < 2 ^ (i - n) := lt_of_lt_of_le hx hpow
        have hbit : ((bits >>> n) % 2).testBit (i - n) = false :=
          Nat.testBit_lt_two_pow hltx
        have hright2 :
            (((bits >>> n) % 2) <<< n).testBit i = false := by
          have hge' : i ≥ n := hge
          simp [Nat.testBit_shiftLeft, hbit]
        simp [Nat.testBit_or, hleft, hright1, hright2]
    | inr hEq =>
        -- `i = n`: left side is `bits.testBit n`
        subst hEq
        have hlt' : n < n + 1 := Nat.lt_succ_self n
        have hleft :
            (bits % 2 ^ (n + 1)).testBit n = bits.testBit n := by
          simp [Nat.testBit_mod_two_pow, hlt']
        have hright1 :
            (bits % 2 ^ n).testBit n = false := by
          have hlt'' : ¬ n < n := Nat.lt_irrefl n
          simp [Nat.testBit_mod_two_pow, hlt'']
        have hshift :
            (((bits >>> n) % 2) <<< n).testBit n = ((bits >>> n) % 2).testBit 0 := by
          simp [Nat.testBit_shiftLeft]
        have hbit0 :
            ((bits >>> n) % 2).testBit 0 = (bits >>> n).testBit 0 := by
          simp
        have hbitn : (bits >>> n).testBit 0 = bits.testBit n := by
          simp
        have hright2 :
            (((bits >>> n) % 2) <<< n).testBit n = bits.testBit n := by
          simp [hshift, hbit0, hbitn]
        -- rewrite both sides explicitly
        rw [hleft]
        simp [Nat.testBit_or, hright1, hright2]

-- Modulo 2^k ignores bits shifted by at least k.
lemma mod_two_pow_or_shift (a b k len : Nat) (hk : k ≤ len) :
    (a ||| (b <<< len)) % 2 ^ k = a % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · have hshift : (b <<< len).testBit i = false := by
      have hle : ¬ i ≥ len := by
        exact not_le_of_gt (lt_of_lt_of_le hi hk)
      simp [Nat.testBit_shiftLeft, hle]
    have hleft := Nat.testBit_mod_two_pow a k i
    have hright := Nat.testBit_mod_two_pow (a ||| (b <<< len)) k i
    have hor : (a ||| (b <<< len)).testBit i = (a.testBit i || (b <<< len).testBit i) := by
      simp [Nat.testBit_or]
    have hor' : (a ||| (b <<< len)).testBit i = a.testBit i := by
      simp [hshift]
    have hleft' : (a % 2 ^ k).testBit i = a.testBit i := by
      simp [hi]
    have hright' : ((a ||| (b <<< len)) % 2 ^ k).testBit i = (a ||| (b <<< len)).testBit i := by
      simp [hi]
    calc
      ((a ||| (b <<< len)) % 2 ^ k).testBit i
          = (a ||| (b <<< len)).testBit i := hright'
      _ = a.testBit i := hor'
      _ = (a % 2 ^ k).testBit i := by symm; exact hleft'
  · have hleft := Nat.testBit_mod_two_pow a k i
    have hright := Nat.testBit_mod_two_pow (a ||| (b <<< len)) k i
    have hleft' : (a % 2 ^ k).testBit i = false := by
      have hnk : ¬ i < k := by exact hi
      simp [hnk]
    have hright' : ((a ||| (b <<< len)) % 2 ^ k).testBit i = false := by
      have hnk : ¬ i < k := by exact hi
      simp [hnk]
    simp [hleft', hright']

-- Shifting right cancels a disjoint left shift.
lemma shiftRight_or_shiftLeft (a b len : Nat) (ha : a < 2 ^ len) :
    (a ||| (b <<< len)) >>> len = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  -- shift-right turns bit `i` into bit `i + len`
  have hshift :
      ((a ||| (b <<< len)) >>> len).testBit i =
        (a ||| (b <<< len)).testBit (len + i) := by
    simp [Nat.testBit_shiftRight]
  -- high bits of `a` are zero
  have hpow : a < 2 ^ (len + i) := by
    have hle : 2 ^ len ≤ 2 ^ (i + len) := by
      have hle' : len ≤ i + len := Nat.le_add_left _ _
      exact Nat.pow_le_pow_of_le (a := 2) (by decide) hle'
    have hle' : 2 ^ (i + len) = 2 ^ (len + i) := by
      simp [Nat.add_comm]
    have hle'' : 2 ^ len ≤ 2 ^ (len + i) := by simpa [hle'] using hle
    exact lt_of_lt_of_le ha hle''
  have hbitA : a.testBit (len + i) = false :=
    Nat.testBit_lt_two_pow hpow
  -- shifted part contributes `b.testBit i`
  have hbitB :
      (b <<< len).testBit (len + i) = b.testBit i := by
    have hge : len + i ≥ len := Nat.le_add_right _ _
    simp [Nat.testBit_shiftLeft, hge]
  -- combine
  have hor :
      (a ||| (b <<< len)).testBit (len + i) =
        (a.testBit (len + i) || (b <<< len).testBit (len + i)) := by
    simp [Nat.testBit_or]
  calc
    ((a ||| (b <<< len)) >>> len).testBit i
        = (a.testBit (len + i) || (b <<< len).testBit (len + i)) := by
            simp [hshift, hor]
    _ = b.testBit i := by
            simp [hbitA, hbitB]

-- OR with a higher shifted bit does not change lower bits.
lemma testBit_or_shiftLeft_lt (x y i j : Nat) (hij : i < j) :
    ((x ||| (y <<< j)).testBit i) = x.testBit i := by
  have hle : ¬ i ≥ j := Nat.not_le_of_gt hij
  have hmask : (y <<< j).testBit i = false := by
    simp [Nat.testBit_shiftLeft, hle]
  have htest := Nat.testBit_or x (y <<< j) i
  simp [hmask]

-- Writing a higher bit does not affect lower bits in a byte.
lemma bit_preserved_or_shift (cur : UInt8) (bitPos bit i : Nat)
    (hi : i < bitPos) (hbit : bitPos < 8) :
    (cur ||| UInt8.ofNat ((bit % 2) <<< bitPos)).toNat.testBit i = cur.toNat.testBit i := by
  have hmask : ((bit % 2) <<< bitPos).testBit i = false := by
    have hle : ¬ i ≥ bitPos := Nat.not_le_of_gt hi
    simp [Nat.testBit_shiftLeft, hle]
  have hmod :
      (((bit % 2) <<< bitPos) % 256).testBit i =
        ((bit % 2) <<< bitPos).testBit i := by
    have hlt : i < 8 := lt_trans hi hbit
    -- `testBit` is preserved under mod 2^8 at bit `i`.
    simpa [Nat.testBit_mod_two_pow, hlt] using
      (Nat.testBit_mod_two_pow ((bit % 2) <<< bitPos) 8 i)
  calc
    (cur ||| UInt8.ofNat ((bit % 2) <<< bitPos)).toNat.testBit i
        = (cur.toNat ||| ((bit % 2) <<< bitPos) % 256).testBit i := by
            simp [UInt8.toNat_or]
    _ = (cur.toNat.testBit i || (((bit % 2) <<< bitPos) % 256).testBit i) := by
            simp [Nat.testBit_or]
    _ = (cur.toNat.testBit i || ((bit % 2) <<< bitPos).testBit i) := by
            simp [hmod]
    _ = cur.toNat.testBit i := by
            simp [hmask]

-- Bit-1 is preserved in the first output byte as bits are written.
def bit1Inv (bw : BitWriter) : Prop :=
  (bw.out.size = 0 ∧ 1 < bw.bitPos ∧ (bw.bitPos < 8) ∧
      bw.cur.toNat.testBit 1 = true) ∨
  (∃ h : 0 < bw.out.size, (bw.out.get 0 h).toNat.testBit 1 = true)

-- Writing a higher bit does not affect bit 1 in the current byte.
lemma bit1_preserved_or_shift (cur : UInt8) (bitPos bit : Nat) (hpos : 1 < bitPos) :
    (cur ||| UInt8.ofNat ((bit % 2) <<< bitPos)).toNat.testBit 1 = cur.toNat.testBit 1 := by
  have hmask : ((bit % 2) <<< bitPos).testBit 1 = false := by
    have hle : ¬ 1 ≥ bitPos := Nat.not_le_of_gt hpos
    simp [Nat.testBit_shiftLeft, hle]
  have hmod :
      (((bit % 2) <<< bitPos) % 256).testBit 1 =
        ((bit % 2) <<< bitPos).testBit 1 := by
    have hlt : 1 < 8 := by decide
    -- `testBit` is preserved under mod 2^8 at bit 1.
    simpa [Nat.testBit_mod_two_pow, hlt] using
      (Nat.testBit_mod_two_pow ((bit % 2) <<< bitPos) 8 1)
  calc
    (cur ||| UInt8.ofNat ((bit % 2) <<< bitPos)).toNat.testBit 1
        = (cur.toNat ||| ((bit % 2) <<< bitPos) % 256).testBit 1 := by
            simp [UInt8.toNat_or]
    _ = (cur.toNat.testBit 1 || (((bit % 2) <<< bitPos) % 256).testBit 1) := by
            simp [Nat.testBit_or]
    _ = (cur.toNat.testBit 1 || ((bit % 2) <<< bitPos).testBit 1) := by
            simp [hmod]
    _ = cur.toNat.testBit 1 := by
            simp [hmask]

-- Invariant: a specific bit in the first output byte is preserved.
def bitPosInv (bw : BitWriter) (out0 pos0 : Nat) (bit : Bool) : Prop :=
  (bw.out.size = out0 ∧ pos0 < bw.bitPos ∧ bw.cur.toNat.testBit pos0 = bit) ∨
  (∃ h : out0 < bw.out.size, (bw.out.get out0 h).toNat.testBit pos0 = bit)

-- Establish the invariant after writing the first bit.
lemma bitPosInv_writeBit_start (bw : BitWriter) (bit : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let out0 := bw.out.size
    let pos0 := bw.bitPos
    bitPosInv (BitWriter.writeBit bw bit) out0 pos0 (decide (bit % 2 = 1)) := by
  -- unfold the lets
  dsimp
  -- compute the written bit in the updated byte
  have hbitnat := bitNat_writeBit bw bit hbit hcur
  let x := (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat
  have hbool : (x.testBit bw.bitPos).toNat = bit % 2 := by
    calc
      (x.testBit bw.bitPos).toNat = ((x >>> bw.bitPos) &&& 1) := by
        symm
        simpa using (bitNat_of_testBit (x := x) (i := bw.bitPos))
      _ = bit % 2 := by
        simpa using hbitnat
  have htest : x.testBit bw.bitPos = decide (bit % 2 = 1) := by
    cases htb : x.testBit bw.bitPos with
    | false =>
        have : bit % 2 = 0 := by simpa [htb] using hbool.symm
        simp [this]
    | true =>
        have : bit % 2 = 1 := by simpa [htb] using hbool.symm
        simp [this]
  by_cases h7 : bw.bitPos = 7
  · -- flushed to out
    right
    have hsize : bw.out.size < (BitWriter.writeBit bw bit).out.size := by
      simp [BitWriter.writeBit, h7, ByteArray.size_push]
    have hget' :
        (bw.out.push (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)))[bw.out.size] =
          (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) := by
      simp [ByteArray.get_push_eq]
    have hget :
        (BitWriter.writeBit bw bit).out.get bw.out.size
            (by
              simp [BitWriter.writeBit, h7, ByteArray.size_push]) =
          (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) := by
      simp [BitWriter.writeBit, h7, byteArray_get_eq_getElem]
    refine ⟨hsize, ?_⟩
    -- rewrite through `hget` to use `htest`
    have hget'' :
        ((BitWriter.writeBit bw bit).out.get bw.out.size
              (by
                simp [BitWriter.writeBit, h7, ByteArray.size_push])).toNat.testBit bw.bitPos =
          x.testBit bw.bitPos := by
      rw [hget]
    exact hget''.trans htest
  · -- stays in cur
    left
    refine ⟨?_, ?_, ?_⟩
    · simp [BitWriter.writeBit, h7]
    · have hpos' : bw.bitPos < bw.bitPos + 1 := Nat.lt_succ_self _
      simp [BitWriter.writeBit, h7]
    · -- rewrite through the updated `cur`
      have hcur' :
          (BitWriter.writeBit bw bit).cur =
            (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) := by
        simp [BitWriter.writeBit, h7]
      have hcur'' :
          (BitWriter.writeBit bw bit).cur.toNat.testBit bw.bitPos =
            (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat.testBit bw.bitPos := by
        simp [hcur']
      have hcur''' :
          (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat.testBit bw.bitPos =
            x.testBit bw.bitPos := by
        rfl
      exact (hcur''.trans hcur''').trans htest

-- The invariant is preserved by writing another bit.
lemma bitPosInv_writeBit (bw : BitWriter) (out0 pos0 : Nat) (bit : Bool) (b : Nat)
    (h : bitPosInv bw out0 pos0 bit) :
    bitPosInv (BitWriter.writeBit bw b) out0 pos0 bit := by
  classical
  cases h with
  | inl h0 =>
      rcases h0 with ⟨hout, hpos, hcur⟩
      -- simplify `out0` to the concrete size
      subst hout
      by_cases h7 : bw.bitPos = 7
      · -- flushes to out
        right
        have hsize : bw.out.size < (BitWriter.writeBit bw b).out.size := by
          -- out size increases by one
          simp [BitWriter.writeBit, h7, ByteArray.size_push]
        have hget' :
            (bw.out.push (bw.cur ||| UInt8.ofNat ((b % 2) <<< bw.bitPos)))[bw.out.size] =
              (bw.cur ||| UInt8.ofNat ((b % 2) <<< bw.bitPos)) := by
          simp [ByteArray.get_push_eq]
        have hget :
            (BitWriter.writeBit bw b).out.get bw.out.size
              (by
                simp [BitWriter.writeBit, h7, ByteArray.size_push]) =
              (bw.cur ||| UInt8.ofNat ((b % 2) <<< bw.bitPos)) := by
          simp [BitWriter.writeBit, h7, byteArray_get_eq_getElem]
        have hbit : bw.bitPos < 8 := bw.hbit
        have hpres :
            (bw.cur ||| UInt8.ofNat ((b % 2) <<< bw.bitPos)).toNat.testBit pos0 = bit := by
          have hpres' :=
            bit_preserved_or_shift (cur := bw.cur) (bitPos := bw.bitPos) (bit := b)
              (i := pos0) hpos hbit
          exact hpres'.trans hcur
        refine ⟨hsize, ?_⟩
        simpa [hget] using hpres
      · -- stays in cur
        left
        have hbit : bw.bitPos < 8 := bw.hbit
        have hpres' :=
          bit_preserved_or_shift (cur := bw.cur) (bitPos := bw.bitPos) (bit := b)
            (i := pos0) hpos hbit
        have hcur' : (BitWriter.writeBit bw b).cur.toNat.testBit pos0 = bit := by
          calc
            (BitWriter.writeBit bw b).cur.toNat.testBit pos0
                = (bw.cur ||| UInt8.ofNat ((b % 2) <<< bw.bitPos)).toNat.testBit pos0 := by
                    simp [BitWriter.writeBit, h7]
            _ = bw.cur.toNat.testBit pos0 := hpres'
            _ = bit := hcur
        refine ⟨?_, ?_, ?_⟩
        · simp [BitWriter.writeBit, h7]
        · have hpos' : pos0 < bw.bitPos + 1 := Nat.lt_succ_of_lt hpos
          simpa [BitWriter.writeBit, h7] using hpos'
        · exact hcur'
  | inr h0 =>
      rcases h0 with ⟨hsize, hbit⟩
      by_cases h7 : bw.bitPos = 7
      · -- flushes, but earlier bytes unchanged
        right
        have hsize' : out0 < (BitWriter.writeBit bw b).out.size := by
          have hsize'' : out0 < bw.out.size + 1 := Nat.lt_trans hsize (Nat.lt_succ_self _)
          simpa [BitWriter.writeBit, h7, ByteArray.size_push] using hsize''
        have hget' :
            (bw.out.push (bw.cur ||| UInt8.ofNat ((b % 2) <<< bw.bitPos)))[out0]'(by
                have : out0 < (bw.out.push (bw.cur ||| UInt8.ofNat ((b % 2) <<< bw.bitPos))).size := by
                  simpa [BitWriter.writeBit, h7, ByteArray.size_push] using hsize'
                simpa [ByteArray.size_push] using this) =
              bw.out[out0]'(by simpa using hsize) := by
          simpa [ByteArray.size_push] using
            (ByteArray.get_push_lt bw.out (bw.cur ||| UInt8.ofNat ((b % 2) <<< bw.bitPos)) out0 hsize)
        have hget :
            (BitWriter.writeBit bw b).out.get out0
                (by
                  simpa [BitWriter.writeBit, h7, ByteArray.size_push] using hsize') =
              bw.out.get out0 hsize := by
          simpa [BitWriter.writeBit, h7, byteArray_get_eq_getElem, byteArray_get_proof_irrel] using hget'
        refine ⟨hsize', ?_⟩
        simpa [hget] using hbit
      · -- out unchanged
        right
        have hsize' : out0 < (BitWriter.writeBit bw b).out.size := by
          simpa [BitWriter.writeBit, h7] using hsize
        have hget :
            (BitWriter.writeBit bw b).out.get out0
                (by simpa [BitWriter.writeBit, h7] using hsize) =
              bw.out.get out0 hsize := by
          simp [BitWriter.writeBit, h7]
        refine ⟨hsize', ?_⟩
        simpa [hget] using hbit

-- Preserve the invariant across multiple bit writes.
lemma bitPosInv_writeBits (bw : BitWriter) (out0 pos0 : Nat) (bit : Bool) (bits len : Nat)
    (h : bitPosInv bw out0 pos0 bit) :
    bitPosInv (BitWriter.writeBits bw bits len) out0 pos0 bit := by
  induction len generalizing bw bits with
  | zero =>
      simpa [BitWriter.writeBits] using h
  | succ n ih =>
      have h' :=
        bitPosInv_writeBit (bw := bw) (out0 := out0) (pos0 := pos0) (bit := bit)
          (b := bits % 2) h
      simpa [BitWriter.writeBits] using
        (ih (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1) h')

-- Extract the preserved bit from the flushed buffer.
lemma bitPosInv_flush (bw : BitWriter) (out0 pos0 : Nat) (bit : Bool)
    (h : bitPosInv bw out0 pos0 bit) (hout : out0 < bw.flush.size) :
    (bw.flush.get out0 hout).toNat.testBit pos0 = bit := by
  cases h with
  | inl h0 =>
      rcases h0 with ⟨hout0, hpos, hcur⟩
      -- simplify `out0` to the concrete size
      subst hout0
      have hbitpos : bw.bitPos ≠ 0 := by
        -- pos0 < bw.bitPos, so bitPos > 0
        exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hpos)
      have hflush : bw.flush = bw.out.push bw.cur := by
        simp [BitWriter.flush, hbitpos]
      have hget' :
          (bw.out.push bw.cur)[bw.out.size] = bw.cur := by
        simp [ByteArray.get_push_eq]
      have hget :
          bw.flush.get bw.out.size hout = bw.cur := by
        -- proof irrelevance for bounds
        have hsize : bw.out.size < (bw.out.push bw.cur).size := by
          simp [ByteArray.size_push]
        -- rewrite via `hflush` and `hget'`
        simp [hflush, byteArray_get_eq_getElem]
      simpa [hget] using hcur
  | inr h0 =>
      rcases h0 with ⟨hsize, hbit⟩
      by_cases hbitpos : bw.bitPos = 0
      · -- flush is just out
        simpa [BitWriter.flush, hbitpos, byteArray_get_proof_irrel] using hbit
      · -- flush pushes current byte, old bytes unchanged
        have hget' :
            (bw.out.push bw.cur)[out0]'(by
                have : out0 < (bw.out.push bw.cur).size := by
                  simpa [ByteArray.size_push] using
                    (Nat.lt_trans hsize (Nat.lt_succ_self _))
                simpa [ByteArray.size_push] using this) =
              bw.out[out0]'(by simpa using hsize) := by
          simpa [ByteArray.size_push] using
            (ByteArray.get_push_lt bw.out bw.cur out0 hsize)
        have hget :
            bw.flush.get out0 hout = bw.out.get out0 hsize := by
          simpa [BitWriter.flush, hbitpos, byteArray_get_eq_getElem, byteArray_get_proof_irrel] using hget'
        simpa [hget] using hbit

-- The extracted bit from the flushed buffer matches the first written bit.
lemma bitNat_writeBits (bw : BitWriter) (bits len : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) (hlen : 0 < len) :
    let bw' := BitWriter.writeBits bw bits len
    have hlt : bw.out.size < bw'.flush.size :=
      flush_size_writeBits_lt bw bits len hlen
    ((bw'.flush.get bw.out.size hlt).toNat >>> bw.bitPos) &&& 1 = bits % 2 := by
  -- unfold len to expose the first bit
  cases len with
  | zero => cases hlen
  | succ n =>
      -- set up the invariant after the first write
      have hstart :
          bitPosInv (BitWriter.writeBit bw (bits % 2)) bw.out.size bw.bitPos (decide (bits % 2 = 1)) := by
        simpa using (bitPosInv_writeBit_start (bw := bw) (bit := bits % 2) hbit hcur)
      -- preserve through the remaining writes
      have hfinal :
          bitPosInv (BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n)
            bw.out.size bw.bitPos (decide (bits % 2 = 1)) := by
        simpa [BitWriter.writeBits] using
          (bitPosInv_writeBits (bw := BitWriter.writeBit bw (bits % 2))
            (out0 := bw.out.size) (pos0 := bw.bitPos) (bit := (decide (bits % 2 = 1)))
            (bits := bits >>> 1) (len := n) hstart)
      -- relate the final writer to `bw'`
      have hbw' :
          BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n =
            BitWriter.writeBits bw bits (Nat.succ n) := by
        simp [BitWriter.writeBits]
      -- extract the preserved bit from the final flush
      have hlt :
          bw.out.size <
            (BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n).flush.size := by
        simpa [hbw'] using (flush_size_writeBits_lt bw bits (Nat.succ n) (by omega))
      have hbit' :
          ((BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n).flush.get
                bw.out.size hlt).toNat.testBit bw.bitPos =
            decide (bits % 2 = 1) := by
        exact bitPosInv_flush
          (bw := BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n)
          (out0 := bw.out.size) (pos0 := bw.bitPos) (bit := (decide (bits % 2 = 1)))
          hfinal hlt
      -- convert testBit to the numeric bit
      have hbool :
          (((BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n).flush.get
                bw.out.size hlt).toNat.testBit bw.bitPos).toNat =
            bits % 2 := by
        -- `bits % 2` is 0 or 1
        have hbool' :
            (((BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n).flush.get
                  bw.out.size hlt).toNat.testBit bw.bitPos).toNat =
              (decide (bits % 2 = 1)).toNat := by
          exact congrArg Bool.toNat hbit'
        cases Nat.mod_two_eq_zero_or_one bits with
        | inl h0 =>
            simpa [h0] using hbool'
        | inr h1 =>
            simpa [h1] using hbool'
      -- rewrite using `bitNat_of_testBit`
      have hbitnat' :
          (((BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n).flush.get
                bw.out.size hlt).toNat >>> bw.bitPos) &&& 1 = bits % 2 := by
        calc
          (((BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n).flush.get
                bw.out.size hlt).toNat >>> bw.bitPos) &&& 1
              = (((BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n).flush.get
                bw.out.size hlt).toNat.testBit bw.bitPos).toNat := by
                  simpa using
                    (bitNat_of_testBit
                      (x := ((BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n).flush.get
                        bw.out.size hlt).toNat)
                      (i := bw.bitPos))
          _ = bits % 2 := hbool
      simpa [hbw'] using hbitnat'

-- Reading the next bit from a reader aligned to a writer after writing `len` bits.
lemma readBit_readerAt_writeBits (bw : BitWriter) (bits len : Nat)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) (hlen : 0 < len) :
    let bw' := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
    br.readBit =
      (bits % 2,
        BitWriter.readerAt (BitWriter.writeBit bw (bits % 2)) bw'.flush
          (by
            -- final flush contains the prefix after the first bit
            cases len with
            | zero => cases hlen
            | succ n =>
                simpa [BitWriter.writeBits] using
                  (flush_size_writeBits_le
                    (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1) (len := n))
          )
          (bitPos_lt_8_writeBit bw (bits % 2) hbit)) := by
  classical
  -- unfold the lets
  dsimp
  have hlt : bw.out.size < (BitWriter.writeBits bw bits len).flush.size :=
    flush_size_writeBits_lt bw bits len hlen
  have hne : bw.out.size ≠ (BitWriter.writeBits bw bits len).flush.size :=
    ne_of_lt hlt
  have hbitnat :
      (((BitWriter.writeBits bw bits len).flush.get bw.out.size hlt).toNat >>> bw.bitPos) &&& 1 =
        bits % 2 := by
    simpa using (bitNat_writeBits bw bits len hbit hcur hlen)
  by_cases h7 : bw.bitPos = 7
  · -- reader advances to next byte
    have hread :
        (BitWriter.readerAt bw (BitWriter.writeBits bw bits len).flush
            (flush_size_writeBits_le bw bits len) hbit).readBit
          = (bits % 2,
              { data := (BitWriter.writeBits bw bits len).flush
                bytePos := bw.out.size + 1
                bitPos := 0
                hpos := by
                  have hle : bw.out.size < (BitWriter.writeBits bw bits len).flush.size := hlt
                  exact Nat.succ_le_of_lt hle
                hend := by intro _; rfl
                hbit := by decide }) := by
      -- reduce the reader; discharge the bit computation via `hbitnat`
      have hbitnat' :
          (((BitWriter.writeBits bw bits len).flush.get bw.out.size hlt).toNat >>> 7) &&& 1 =
            bits % 2 := by
        simpa [h7] using hbitnat
      simp [BitWriter.readerAt, BitReader.readBit, hne, h7, hbitnat',
        -UInt8.toNat_or, -UInt8.ofNat_shiftLeft, -Nat.and_one_is_mod]
    have hreader :
        ( { data := (BitWriter.writeBits bw bits len).flush
            bytePos := bw.out.size + 1
            bitPos := 0
            hpos := by
              have hle : bw.out.size < (BitWriter.writeBits bw bits len).flush.size := hlt
              exact Nat.succ_le_of_lt hle
            hend := by intro _; rfl
            hbit := by decide } : BitReader)
          =
          BitWriter.readerAt (BitWriter.writeBit bw (bits % 2))
            (BitWriter.writeBits bw bits len).flush
            (by
              cases len with
              | zero => cases hlen
              | succ n =>
                  simpa [BitWriter.writeBits] using
                    (flush_size_writeBits_le
                      (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1) (len := n)))
            (bitPos_lt_8_writeBit bw (bits % 2) hbit) := by
      apply BitReader.ext <;> simp [BitWriter.readerAt, BitWriter.writeBit, h7]
    simp [hread, hreader]
  · -- reader stays in the same byte
    have hread :
        (BitWriter.readerAt bw (BitWriter.writeBits bw bits len).flush
            (flush_size_writeBits_le bw bits len) hbit).readBit
          = (bits % 2,
              { data := (BitWriter.writeBits bw bits len).flush
                bytePos := bw.out.size
                bitPos := bw.bitPos + 1
                hpos := by
                  have hpos' : bw.out.size ≤ (BitWriter.writeBits bw bits len).flush.size := by
                    have hpos' : bw.out.size ≤ bw.flush.size := out_size_le_flush bw
                    exact le_trans hpos' (flush_size_writeBits_le bw bits len)
                  simpa using hpos'
                hend := by
                  intro hEq
                  have hlt : bw.out.size < (BitWriter.writeBits bw bits len).flush.size := hlt
                  exact (False.elim ((Nat.ne_of_lt hlt) hEq))
                hbit := by
                  have hlt' : bw.bitPos < 7 := by
                    exact lt_of_le_of_ne (Nat.le_of_lt_succ hbit) h7
                  have hbit' : bw.bitPos + 1 < 8 := by
                    simpa [Nat.succ_eq_add_one] using (Nat.succ_lt_succ_iff.mpr hlt')
                  simpa [Nat.add_comm] using hbit' }) := by
      simp [BitWriter.readerAt, BitReader.readBit, hne, h7, hbitnat,
        -UInt8.toNat_or, -UInt8.ofNat_shiftLeft, -Nat.and_one_is_mod]
    have hreader :
        ( { data := (BitWriter.writeBits bw bits len).flush
            bytePos := bw.out.size
            bitPos := bw.bitPos + 1
            hpos := by
              have hpos' : bw.out.size ≤ (BitWriter.writeBits bw bits len).flush.size := by
                have hpos' : bw.out.size ≤ bw.flush.size := out_size_le_flush bw
                exact le_trans hpos' (flush_size_writeBits_le bw bits len)
              simpa using hpos'
            hend := by
              intro hEq
              have hlt : bw.out.size < (BitWriter.writeBits bw bits len).flush.size := hlt
              exact (False.elim ((Nat.ne_of_lt hlt) hEq))
            hbit := by
              have hlt' : bw.bitPos < 7 := by
                exact lt_of_le_of_ne (Nat.le_of_lt_succ hbit) h7
              have hbit' : bw.bitPos + 1 < 8 := by
                simpa [Nat.succ_eq_add_one] using (Nat.succ_lt_succ_iff.mpr hlt')
              simpa [Nat.add_comm] using hbit' } : BitReader)
          =
          BitWriter.readerAt (BitWriter.writeBit bw (bits % 2))
            (BitWriter.writeBits bw bits len).flush
            (by
              cases len with
              | zero => cases hlen
              | succ n =>
                  simpa [BitWriter.writeBits] using
                    (flush_size_writeBits_le
                      (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1) (len := n)))
            (bitPos_lt_8_writeBit bw (bits % 2) hbit) := by
      apply BitReader.ext <;> simp [BitWriter.readerAt, BitWriter.writeBit, h7]
    simp [hread, hreader]

-- Split a `writeBits` call into a prefix and suffix.
lemma writeBits_split (bw : BitWriter) (bits k n : Nat) :
    BitWriter.writeBits bw bits (k + n) =
      BitWriter.writeBits (BitWriter.writeBits bw bits k) (bits >>> k) n := by
  induction k generalizing bw bits with
  | zero =>
      simp [BitWriter.writeBits]
  | succ k ih =>
      -- unroll one step and use the induction hypothesis
      have hshift : (bits >>> 1) >>> k = bits >>> (k + 1) := by
        -- shift-right is additive in the shift amount
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.shiftRight_add bits 1 k).symm
      calc
        BitWriter.writeBits bw bits (Nat.succ k + n)
            = BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) (k + n) := by
                simp [BitWriter.writeBits, Nat.succ_add]
        _ = BitWriter.writeBits
              (BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) k)
              ((bits >>> 1) >>> k) n := by
                simpa using (ih (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1))
        _ = BitWriter.writeBits (BitWriter.writeBits bw bits (Nat.succ k)) (bits >>> (Nat.succ k)) n := by
                simp [BitWriter.writeBits, hshift, Nat.succ_eq_add_one]

-- `writeBits` depends only on the low `len` bits.
lemma writeBits_mod (bw : BitWriter) (bits len : Nat) :
    BitWriter.writeBits bw bits len = BitWriter.writeBits bw (bits % 2 ^ len) len := by
  induction len generalizing bw bits with
  | zero =>
      simp [BitWriter.writeBits]
  | succ n ih =>
      have hdecomp :
          bits % 2 ^ (n + 1) =
            (bits % 2) ||| (((bits >>> 1) % 2 ^ n) <<< 1) := mod_two_pow_decomp bits n
      have hbit :
          (bits % 2 ^ (n + 1)) % 2 = bits % 2 := by
        have hmod :=
          mod_two_pow_or_shift (a := bits % 2) (b := (bits >>> 1) % 2 ^ n) (k := 1) (len := 1) (by decide)
        have hlt : bits % 2 < 2 ^ (1 : Nat) := by
          have : bits % 2 < 2 := Nat.mod_lt _ (by decide)
          simpa using this
        have hmod' : (bits % 2) % 2 ^ (1 : Nat) = bits % 2 := Nat.mod_eq_of_lt hlt
        simpa [hdecomp, hmod'] using hmod
      have hshift :
          (bits % 2 ^ (n + 1)) >>> 1 = (bits >>> 1) % 2 ^ n := by
        have hlt : bits % 2 < 2 ^ (1 : Nat) := by
          have : bits % 2 < 2 := Nat.mod_lt _ (by decide)
          simpa using this
        -- use the low-bit decomposition and cancel the shift
        have h := shiftRight_or_shiftLeft (a := bits % 2) (b := (bits >>> 1) % 2 ^ n) (len := 1) hlt
        simpa [hdecomp] using h
      calc
        BitWriter.writeBits bw bits (n + 1)
            = BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) n := by
                simp [BitWriter.writeBits]
        _ = BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) ((bits >>> 1) % 2 ^ n) n := by
                simpa using (ih (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1))
        _ = BitWriter.writeBits (BitWriter.writeBit bw ((bits % 2 ^ (n + 1)) % 2))
              ((bits % 2 ^ (n + 1)) >>> 1) n := by
                simp [hbit, hshift]
        _ = BitWriter.writeBits bw (bits % 2 ^ (n + 1)) (n + 1) := by
                simp [BitWriter.writeBits]

lemma writeBits_align8 (bw : BitWriter) (bits : Nat) (hpos : bw.bitPos = 0) :
    BitWriter.writeBits bw bits 8 =
      { out := bw.out.push
          (bw.cur ||| UInt8.ofNat (bits % 2) |||
            (UInt8.ofNat ((bits >>> 1) % 2) <<< 1) |||
            (UInt8.ofNat ((bits >>> 1 >>> 1) % 2) <<< 2) |||
            (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1) % 2) <<< 3) |||
            (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 4) |||
            (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 5) |||
            (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 6) |||
            (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 7)),
        cur := 0, bitPos := 0, hbit := by decide } := by
  -- Unfold the 8 steps; `simp` resolves all bitPos cases from `hpos`.
  simp [BitWriter.writeBits, BitWriter.writeBit, hpos, Nat.add_comm]

lemma writeBits_small (bw : BitWriter) (bits len : Nat) (hsmall : bw.bitPos + len < 8) :
    BitWriter.writeBits bw bits len =
      { out := bw.out,
        cur := packBitsAccU8 bits len bw.bitPos bw.cur,
        bitPos := bw.bitPos + len,
        hbit := by omega } := by
  induction len generalizing bw bits with
  | zero =>
      simp [BitWriter.writeBits, packBitsAccU8]
  | succ n ih =>
      have hpos : bw.bitPos ≠ 7 := by omega
      have hsmall' : (BitWriter.writeBit bw (bits % 2)).bitPos + n < 8 := by
        have hbitpos :
            (BitWriter.writeBit bw (bits % 2)).bitPos = bw.bitPos + 1 := by
          simp [BitWriter.writeBit, hpos]
        have hlt : bw.bitPos + 1 + n < 8 := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsmall
        simpa [hbitpos, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
      have ih' := ih (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1) hsmall'
      -- unfold one step of `writeBits`, then apply the IH
      simp [BitWriter.writeBits, BitWriter.writeBit, hpos]
      simpa [BitWriter.writeBit, hpos, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih'

lemma writeBitsFast_eq_writeBits (bw : BitWriter) (bits len : Nat) :
    BitWriter.writeBitsFast bw bits len = BitWriter.writeBits bw bits len := by
  classical
  -- Strong induction on `len` because the fast path subtracts 8.
  revert bw bits
  refine Nat.strong_induction_on len ?_
  intro n ih bw bits
  by_cases hfast : bw.bitPos = 0 ∧ 8 ≤ n
  · -- fast path: peel off 8 bits, then apply IH
    by_cases hlen8 : n = 8
    · subst hlen8
      have h8 := writeBits_align8 bw bits hfast.1
      simp [BitWriter.writeBitsFast, hfast, h8]
    · by_cases hlen9 : n = 9
      · subst hlen9
        have h8 := writeBits_align8 bw bits hfast.1
        let bw8 : BitWriter :=
          { out := bw.out.push
              (bw.cur ||| UInt8.ofNat (bits % 2) |||
                (UInt8.ofNat ((bits >>> 1) % 2) <<< 1) |||
                (UInt8.ofNat ((bits >>> 1 >>> 1) % 2) <<< 2) |||
                (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1) % 2) <<< 3) |||
                (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 4) |||
                (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 5) |||
                (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 6) |||
                (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 7)),
            cur := 0, bitPos := 0, hbit := by decide }
        have h8' : BitWriter.writeBits bw bits 8 = bw8 := by
          simpa [bw8] using h8
        have hsplit := writeBits_split bw bits 8 1
        have hsmall : bw8.bitPos + 1 < 8 := by
          simp [bw8]
        have h1 := writeBits_small (bw := bw8) (bits := bits >>> 8) (len := 1) hsmall
        have hpack :
            packBitsAccU8 (bits >>> 8) 1 bw8.bitPos bw8.cur =
              UInt8.ofNat ((bits >>> 8) % 2) := by
          simp [bw8, packBitsAccU8]
        have hwrite9 :
            BitWriter.writeBits bw bits 9 =
              { out := bw.out.push
                  (bw.cur ||| UInt8.ofNat (bits % 2) |||
                    (UInt8.ofNat ((bits >>> 1) % 2) <<< 1) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1) % 2) <<< 2) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1) % 2) <<< 3) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 4) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 5) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 6) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 7)),
                cur := UInt8.ofNat ((bits >>> 8) % 2),
                bitPos := 1,
                hbit := by decide } := by
          -- split into 8 bits + 1 bit
          calc
            BitWriter.writeBits bw bits 9
                = BitWriter.writeBits (BitWriter.writeBits bw bits 8) (bits >>> 8) 1 := by
                    simpa using hsplit
            _ = BitWriter.writeBits bw8 (bits >>> 8) 1 := by
                    simp [h8']
            _ = { out := bw8.out,
                  cur := packBitsAccU8 (bits >>> 8) 1 bw8.bitPos bw8.cur,
                  bitPos := bw8.bitPos + 1,
                  hbit := by omega } := by
                    simpa using h1
            _ = { out := bw.out.push
                    (bw.cur ||| UInt8.ofNat (bits % 2) |||
                      (UInt8.ofNat ((bits >>> 1) % 2) <<< 1) |||
                      (UInt8.ofNat ((bits >>> 1 >>> 1) % 2) <<< 2) |||
                      (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1) % 2) <<< 3) |||
                      (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 4) |||
                      (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 5) |||
                      (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 6) |||
                      (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 7)),
                  cur := UInt8.ofNat ((bits >>> 8) % 2),
                  bitPos := 1,
                  hbit := by decide } := by
                    simp [bw8, hpack]
        simpa [BitWriter.writeBitsFast, hfast, hlen8] using hwrite9.symm
      · -- general recursive case
        have hlen : n = 8 + (n - 8) := by
          have hle : 8 ≤ n := hfast.2
          exact (Nat.add_sub_of_le hle).symm
        -- compute the first byte via `writeBits`
        have h8 : BitWriter.writeBits bw bits 8 =
            { out := bw.out.push
                (bw.cur ||| UInt8.ofNat (bits % 2) |||
                  (UInt8.ofNat ((bits >>> 1) % 2) <<< 1) |||
                  (UInt8.ofNat ((bits >>> 1 >>> 1) % 2) <<< 2) |||
                  (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1) % 2) <<< 3) |||
                  (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 4) |||
                  (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 5) |||
                  (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 6) |||
                  (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 7)),
              cur := 0, bitPos := 0, hbit := by decide } := by
          exact writeBits_align8 bw bits hfast.1
        -- split the slow writer
        have hsplit :
            BitWriter.writeBits bw bits n =
              BitWriter.writeBits (BitWriter.writeBits bw bits 8) (bits >>> 8) (n - 8) := by
          -- use the split lemma with k=8
          have hsplit0 := writeBits_split bw bits 8 (n - 8)
          simpa [← hlen] using hsplit0
        -- apply IH on the remainder
        have hrec :
            BitWriter.writeBitsFast
              { out := bw.out.push
                  (bw.cur ||| UInt8.ofNat (bits % 2) |||
                    (UInt8.ofNat ((bits >>> 1) % 2) <<< 1) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1) % 2) <<< 2) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1) % 2) <<< 3) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 4) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 5) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 6) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 7)),
                cur := 0, bitPos := 0, hbit := by decide }
              (bits >>> 8) (n - 8) =
            BitWriter.writeBits
              { out := bw.out.push
                  (bw.cur ||| UInt8.ofNat (bits % 2) |||
                    (UInt8.ofNat ((bits >>> 1) % 2) <<< 1) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1) % 2) <<< 2) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1) % 2) <<< 3) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 4) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 5) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 6) |||
                    (UInt8.ofNat ((bits >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1) % 2) <<< 7)),
                cur := 0, bitPos := 0, hbit := by decide }
              (bits >>> 8) (n - 8) := by
          -- `n - 8 < n` when `8 ≤ n`
          have hlt : n - 8 < n := by omega
          exact ih (n - 8) hlt _ _
        -- finish
        simp [BitWriter.writeBitsFast, hfast, hlen8, hlen9, h8, hsplit, hrec]
  · by_cases hsmall : bw.bitPos + n < 8
    · have hsmall' : bw.bitPos + n < 8 := hsmall
      simp [BitWriter.writeBitsFast, hfast, hsmall, writeBits_small (bw := bw) (bits := bits) (len := n) hsmall']
    · simp [BitWriter.writeBitsFast, hfast, hsmall]

attribute [simp] writeBitsFast_eq_writeBits

-- Writing concatenated bitstrings equals sequential writes.
lemma writeBits_concat (bw : BitWriter) (bits rest len restLen : Nat)
    (hbits : bits < 2 ^ len) :
    BitWriter.writeBits bw (bits ||| (rest <<< len)) (len + restLen) =
      BitWriter.writeBits (BitWriter.writeBits bw bits len) rest restLen := by
  have hsplit :=
    writeBits_split bw (bits ||| (rest <<< len)) len restLen
  -- simplify the prefix
  have hmod : (bits ||| (rest <<< len)) % 2 ^ len = bits := by
    have hmod' := mod_two_pow_or_shift bits rest len len (by exact le_rfl)
    have hbits' : bits % 2 ^ len = bits := Nat.mod_eq_of_lt hbits
    simpa [hbits'] using hmod'
  have hprefix :
      BitWriter.writeBits bw (bits ||| (rest <<< len)) len = BitWriter.writeBits bw bits len := by
    calc
      BitWriter.writeBits bw (bits ||| (rest <<< len)) len
          = BitWriter.writeBits bw ((bits ||| (rest <<< len)) % 2 ^ len) len := by
              simpa using (writeBits_mod bw (bits ||| (rest <<< len)) len)
      _ = BitWriter.writeBits bw bits len := by
              simp [hmod]
  have hshift : (bits ||| (rest <<< len)) >>> len = rest :=
    shiftRight_or_shiftLeft bits rest len hbits
  -- assemble
  calc
    BitWriter.writeBits bw (bits ||| (rest <<< len)) (len + restLen)
        = BitWriter.writeBits (BitWriter.writeBits bw (bits ||| (rest <<< len)) len)
            ((bits ||| (rest <<< len)) >>> len) restLen := hsplit
    _ = BitWriter.writeBits (BitWriter.writeBits bw bits len) rest restLen := by
          simp [hprefix, hshift]

-- Flush size is monotone in the number of bits written.
lemma flush_size_writeBits_prefix (bw : BitWriter) (bits k len : Nat) (hk : k ≤ len) :
    (BitWriter.writeBits bw bits k).flush.size ≤
      (BitWriter.writeBits bw bits len).flush.size := by
  have hlen : k + (len - k) = len := Nat.add_sub_of_le hk
  have hsplit :
      BitWriter.writeBits bw bits len =
        BitWriter.writeBits (BitWriter.writeBits bw bits k) (bits >>> k) (len - k) := by
    simpa [hlen] using (writeBits_split bw bits k (len - k))
  have hle :
      (BitWriter.writeBits bw bits k).flush.size ≤
        (BitWriter.writeBits (BitWriter.writeBits bw bits k) (bits >>> k) (len - k)).flush.size := by
    simpa using
      (flush_size_writeBits_le (bw := BitWriter.writeBits bw bits k) (bits := bits >>> k) (len := len - k))
  simpa [hsplit] using hle

-- Bounds for reading the first `k` bits from a stream produced by `writeBits`.
lemma readerAt_writeBits_bound (bw : BitWriter) (bits len k : Nat) (hk : k ≤ len)
    (hbit : bw.bitPos < 8) :
    let bw' := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
    br.bitIndex + k ≤ br.data.size * 8 := by
  dsimp
  have hbit' : (BitWriter.writeBits bw bits len).bitPos < 8 :=
    bitPos_lt_8_writeBits bw bits len hbit
  have hle1 : bw.bitCount + k ≤ bw.bitCount + len := by
    exact Nat.add_le_add_left hk _
  have hle2 : bw.bitCount + k ≤ (BitWriter.writeBits bw bits len).bitCount := by
    simpa [bitCount_writeBits] using hle1
  have hle3 :
      (BitWriter.writeBits bw bits len).bitCount ≤
        (BitWriter.writeBits bw bits len).flush.size * 8 := by
    simpa using (flush_size_mul_ge_bitCount (bw := BitWriter.writeBits bw bits len) hbit')
  simpa [BitWriter.readerAt, BitReader.bitIndex, BitWriter.bitCount] using
    (le_trans hle2 hle3)

-- Reading the first `k` bits from a stream produced by `writeBits`.
lemma readBits_proof_irrel (br : BitReader) (n : Nat)
    (h1 h2 : br.bitIndex + n ≤ br.data.size * 8) :
    br.readBits n h1 = br.readBits n h2 := by
  cases (Subsingleton.elim h1 h2)
  rfl

lemma proof_irrel_fun {α} {p : Prop} (f : p → α) (h1 h2 : p) : f h1 = f h2 := by
  cases (Subsingleton.elim h1 h2)
  rfl

lemma shiftLeft_shiftLeft (a b c : Nat) : (a <<< b) <<< c = a <<< (b + c) := by
  simp [Nat.shiftLeft_eq, Nat.mul_assoc, Nat.pow_add]

lemma readBitsAuxAcc_eq (br : BitReader) (n shift acc : Nat) :
    BitReader.readBitsAuxAcc br n shift acc =
      let (rest, br') := BitReader.readBitsAuxAcc br n 0 0
      (acc ||| (rest <<< shift), br') := by
  induction n generalizing br shift acc with
  | zero =>
      simp [BitReader.readBitsAuxAcc]
  | succ n ih =>
      cases hbit : br.readBit with
      | mk bit br' =>
          simp [BitReader.readBitsAuxAcc, hbit]
          cases hrest : BitReader.readBitsAuxAcc br' n 0 0 with
          | mk rest0 br'' =>
              have hL :
                  BitReader.readBitsAuxAcc br' n (shift + 1) (acc ||| (bit <<< shift)) =
                    ((acc ||| (bit <<< shift)) ||| (rest0 <<< (shift + 1)), br'') := by
                simpa [hrest] using
                  (ih (br := br') (shift := shift + 1) (acc := acc ||| (bit <<< shift)))
              have h1 :=
                ih (br := br') (shift := 1) (acc := bit)
              have h1' :
                  BitReader.readBitsAuxAcc br' n 1 bit = (bit ||| (rest0 <<< 1), br'') := by
                simpa [hrest] using h1
              have hR' :
                  ((acc ||| (bit <<< shift)) ||| (rest0 <<< (shift + 1))) =
                    acc ||| ((bit ||| (rest0 <<< 1)) <<< shift) := by
                calc
                  (acc ||| (bit <<< shift)) ||| (rest0 <<< (shift + 1))
                      = acc ||| ((bit <<< shift) ||| (rest0 <<< (shift + 1))) := by
                          simp [Nat.or_assoc]
                  _ = acc ||| ((bit <<< shift) ||| (rest0 <<< (1 + shift))) := by
                          simp [Nat.add_comm]
                  _ = acc ||| ((bit <<< shift) ||| ((rest0 <<< 1) <<< shift)) := by
                          simp [shiftLeft_shiftLeft]
                  _ = acc ||| ((bit ||| (rest0 <<< 1)) <<< shift) := by
                          simp [Nat.shiftLeft_or_distrib]
              -- combine and normalize bitwise shifts
              have hcalc :
                  BitReader.readBitsAuxAcc br' n (shift + 1) (acc ||| (bit <<< shift)) =
                    (acc ||| ((bit ||| (rest0 <<< 1)) <<< shift), br'') := by
                calc
                  BitReader.readBitsAuxAcc br' n (shift + 1) (acc ||| (bit <<< shift))
                      = ((acc ||| (bit <<< shift)) ||| (rest0 <<< (shift + 1)), br'') := hL
                  _ = (acc ||| ((bit ||| (rest0 <<< 1)) <<< shift), br'') := by
                        exact congrArg (fun x => (x, br'')) hR'
              simpa [h1'] using hcalc

lemma readBitsAux_succ (br : BitReader) (k : Nat) :
    BitReader.readBitsAux br (k + 1) =
      let (bit, br') := br.readBit
      let (rest, br'') := BitReader.readBitsAux br' k
      (bit ||| (rest <<< 1), br'') := by
  unfold BitReader.readBitsAux
  cases hbit : br.readBit with
  | mk bit br' =>
      simp [BitReader.readBitsAuxAcc, hbit]
      simpa using (readBitsAuxAcc_eq (br := br') (n := k) (shift := 1) (acc := bit))

lemma readBits_succ_eq (br : BitReader) (k : Nat)
    (h : br.bitIndex + (k + 1) ≤ br.data.size * 8)
    (bit : Nat) (br' : BitReader) (hbit : br.readBit = (bit, br'))
    (hread' : br'.bitIndex + k ≤ br'.data.size * 8) :
    br.readBits (k + 1) h =
      (bit ||| ((br'.readBits k hread').1 <<< 1), (br'.readBits k hread').2) := by
  -- unfold one step of `readBits`
  simp [BitReader.readBits, readBitsAux_succ, hbit]

lemma readBits_readerAt_writeBits_prefix (bw : BitWriter) (bits len k : Nat)
    (hk : k ≤ len) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bw' := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
    ∀ {hread : br.bitIndex + k ≤ br.data.size * 8},
      br.readBits k hread =
        (bits % 2 ^ k,
          BitWriter.readerAt (BitWriter.writeBits bw bits k) bw'.flush
            (flush_size_writeBits_prefix bw bits k len hk)
            (bitPos_lt_8_writeBits bw bits k hbit)) := by
  classical
  -- unfold the lets
  dsimp
  intro hread
  -- induction on `k`
  induction k generalizing bw bits len with
  | zero =>
      -- `readBits 0` returns the current reader
      simp [BitReader.readBits, BitReader.readBitsAux, BitReader.readBitsAuxAcc,
        BitWriter.writeBits, Nat.mod_one]
  | succ k ih =>
      -- `len` must be positive
      cases len with
      | zero =>
          cases (Nat.not_succ_le_zero _ hk)
      | succ len =>
          have hk' : k ≤ len := by
            exact (Nat.succ_le_succ_iff.mp hk)
          -- compute the first bit
          have hlen : 0 < Nat.succ len := Nat.succ_pos _
          have hreadbit :=
            readBit_readerAt_writeBits (bw := bw) (bits := bits) (len := Nat.succ len) hbit hcur hlen
          let br1 :=
            BitWriter.readerAt (BitWriter.writeBit bw (bits % 2))
              (BitWriter.writeBits (BitWriter.writeBit bw (bits % 2)) (bits >>> 1) len).flush
              (flush_size_writeBits_le (bw := BitWriter.writeBit bw (bits % 2))
                (bits := bits >>> 1) (len := len))
              (bitPos_lt_8_writeBit bw (bits % 2) hbit)
          have hreadbit' :
              (BitWriter.readerAt bw (BitWriter.writeBits bw bits (Nat.succ len)).flush
                  (flush_size_writeBits_le bw bits (Nat.succ len)) hbit).readBit =
                (bits % 2, br1) := by
            simpa [br1, BitWriter.writeBits] using hreadbit
          have hreadbit_fst :
              (BitWriter.readerAt bw (BitWriter.writeBits bw bits (Nat.succ len)).flush
                  (flush_size_writeBits_le bw bits (Nat.succ len)) hbit).readBit.fst = bits % 2 := by
            simpa using congrArg Prod.fst hreadbit'
          have hreadbit_snd :
              (BitWriter.readerAt bw (BitWriter.writeBits bw bits (Nat.succ len)).flush
                  (flush_size_writeBits_le bw bits (Nat.succ len)) hbit).readBit.snd = br1 := by
            simpa using congrArg Prod.snd hreadbit'
          have hread' : br1.bitIndex + k ≤ br1.data.size * 8 := by
            simpa [br1] using
              (readerAt_writeBits_bound
                (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1) (len := len) (k := k)
                (hk := hk') (hbit := bitPos_lt_8_writeBit bw (bits % 2) hbit))
          have ih' :=
            ih (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1) (len := len)
              (hk := hk') (hbit := bitPos_lt_8_writeBit bw (bits % 2) hbit)
              (hcur := curClearAbove_writeBit bw (bits % 2) hbit hcur) (hread := hread')
          -- use the single-step `readBits` equation
          have hcalc :=
            readBits_succ_eq
              (br := BitWriter.readerAt bw (BitWriter.writeBits bw bits (Nat.succ len)).flush
                (flush_size_writeBits_le bw bits (Nat.succ len)) hbit)
              (k := k) (h := hread) (bit := bits % 2) (br' := br1) hreadbit' hread'
          simpa [mod_two_pow_decomp, ih', br1, BitWriter.writeBits] using hcalc

lemma bit1Inv_writeBit (bw : BitWriter) (bit : Nat) (h : bit1Inv bw) :
    bit1Inv (BitWriter.writeBit bw bit) := by
  classical
  cases h with
  | inl h0 =>
      rcases h0 with ⟨hout, hpos, hlt8, hcur1⟩
      by_cases h7 : bw.bitPos = 7
      · -- flushes to out
        right
        have hsize : 0 < (BitWriter.writeBit bw bit).out.size := by
          -- out := bw.out.push ...
          simp [BitWriter.writeBit, h7, ByteArray.size_push]
        have hcur1' :
            (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat.testBit 1 = true := by
          rw [bit1_preserved_or_shift (cur := bw.cur) (bitPos := bw.bitPos) (bit := bit) hpos]
          exact hcur1
        refine ⟨hsize, ?_⟩
        -- first byte is the pushed byte (bw.out is empty)
        have hget' :
            (bw.out.push (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)))[0] =
              (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) := by
          simpa [hout] using
            (ByteArray.get_push_eq bw.out (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)))
        have hget :
            (BitWriter.writeBit bw bit).out.get 0
                (by
                  simp [BitWriter.writeBit, h7, ByteArray.size_push]) =
              (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) := by
          simpa [BitWriter.writeBit, h7, byteArray_get_eq_getElem] using hget'
        calc
          ((BitWriter.writeBit bw bit).out.get 0
              (by
                simp [BitWriter.writeBit, h7, ByteArray.size_push])).toNat.testBit 1
              = (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat.testBit 1 := by
                  rw [hget]
          _ = true := hcur1'
      · -- stays in cur
        left
        have hcur1' :
            (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)).toNat.testBit 1 = true := by
          rw [bit1_preserved_or_shift (cur := bw.cur) (bitPos := bw.bitPos) (bit := bit) hpos]
          exact hcur1
        have hpos' : 1 < bw.bitPos + 1 := by omega
        have hlt8' : bw.bitPos + 1 < 8 := by omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [BitWriter.writeBit, hout, h7]
        · simpa [BitWriter.writeBit, h7] using hpos'
        · simpa [BitWriter.writeBit, h7] using hlt8'
        · simpa [BitWriter.writeBit, h7] using hcur1'
  | inr h0 =>
      -- out already has first byte set
      rcases h0 with ⟨hsize, hbit1⟩
      by_cases h7 : bw.bitPos = 7
      · right
        have hsize' : 0 < (BitWriter.writeBit bw bit).out.size := by
          simp [BitWriter.writeBit, h7, ByteArray.size_push]
        refine ⟨hsize', ?_⟩
        -- byte 0 unchanged by push
        have hget' :
            (bw.out.push (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)))[0]'(by
                simp [ByteArray.size_push]) =
              bw.out[0]'hsize := by
          simpa [ByteArray.size_push] using
            (ByteArray.get_push_lt bw.out (bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)) 0 hsize)
        have hget :
            (BitWriter.writeBit bw bit).out.get 0
                (by
                  simp [BitWriter.writeBit, h7, ByteArray.size_push]) =
              bw.out.get 0 hsize := by
          simpa [BitWriter.writeBit, h7, byteArray_get_eq_getElem, byteArray_get_proof_irrel] using hget'
        simpa [hget] using hbit1
      · right
        have hsize' : 0 < (BitWriter.writeBit bw bit).out.size := by
          simpa [BitWriter.writeBit, h7] using hsize
        refine ⟨hsize', ?_⟩
        simpa [BitWriter.writeBit, h7, byteArray_get_proof_irrel] using hbit1

lemma bit1Inv_writeBits (bw : BitWriter) (bits len : Nat) (h : bit1Inv bw) :
    bit1Inv (BitWriter.writeBits bw bits len) := by
  induction len generalizing bw bits with
  | zero =>
      simpa [BitWriter.writeBits] using h
  | succ n ih =>
      have h' := bit1Inv_writeBit bw (bits % 2) h
      simpa [BitWriter.writeBits] using
        (ih (bw := BitWriter.writeBit bw (bits % 2)) (bits := bits >>> 1) h')

lemma bit1Inv_deflateFixedAux (data : Array UInt8) (i : Nat) (bw : BitWriter)
    (h : bit1Inv bw) : bit1Inv (deflateFixedAux data i bw) := by
  classical
  have hk :
      ∀ k, ∀ i bw, data.size - i = k → bit1Inv bw →
        bit1Inv (deflateFixedAux data i bw) := by
    intro k
    induction k with
    | zero =>
        intro i bw hk hbw
        have hle : data.size ≤ i := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ i < data.size := not_lt_of_ge hle
        simp [deflateFixedAux, hlt, hbw]
    | succ k ih =>
        intro i bw hk hbw
        by_cases hlt : i < data.size
        · have hk' : data.size - (i + 1) = k := by
            have : data.size - i = k + 1 := hk
            omega
          let b := data[i]
          let codeLen := fixedLitLenCode b.toNat
          let code := codeLen.1
          let len := codeLen.2
          have h' : bit1Inv (bw.writeBits (reverseBits code len) len) := by
            simpa [code, len] using (bit1Inv_writeBits bw (reverseBits code len) len hbw)
          have ih' :=
            ih (i := i + 1) (bw := bw.writeBits (reverseBits code len) len) hk' h'
          -- Unfold only the outer call.
          rw [deflateFixedAux.eq_1]
          simp [hlt]
          exact ih'
        · simp [deflateFixedAux, hlt, hbw]
  exact hk (data.size - i) i bw rfl h

lemma bit1Inv_deflateFixed_header :
    let bw0 := BitWriter.empty
    let bw1 := bw0.writeBits 1 1
    let bw2 := bw1.writeBits 1 2
    bit1Inv bw2 := by
  -- Compute the header bits explicitly.
  left
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [BitWriter.empty, BitWriter.writeBits, BitWriter.writeBit]
  · decide
  · decide
  · decide

lemma bit1Inv_deflateFixed (raw : ByteArray) :
    let bw0 := BitWriter.empty
    let bw1 := bw0.writeBits 1 1
    let bw2 := bw1.writeBits 1 2
    let bw3 := deflateFixedAux raw.data 0 bw2
    let (eobCode, eobLen) := fixedLitLenCode 256
    let bw4 := bw3.writeBits (reverseBits eobCode eobLen) eobLen
    bit1Inv bw4 := by
  -- Start from the fixed header, then preserve through payload and EOB.
  have h2 : bit1Inv (BitWriter.writeBits (BitWriter.writeBits BitWriter.empty 1 1) 1 2) := by
    simpa using bit1Inv_deflateFixed_header
  -- Payload
  have h3 : bit1Inv (deflateFixedAux raw.data 0
      (BitWriter.writeBits (BitWriter.writeBits BitWriter.empty 1 1) 1 2)) := by
    simpa using
      (bit1Inv_deflateFixedAux (data := raw.data) (i := 0)
        (bw := BitWriter.writeBits (BitWriter.writeBits BitWriter.empty 1 1) 1 2) h2)
  -- EOB
  cases hlen : fixedLitLenCode 256 with
  | mk eobCode eobLen =>
      -- `simp` will rewrite the lets
      simpa [BitWriter.writeBits, hlen] using
        (bit1Inv_writeBits
          (bw := deflateFixedAux raw.data 0
            (BitWriter.writeBits (BitWriter.writeBits BitWriter.empty 1 1) 1 2))
          (bits := reverseBits eobCode eobLen) (len := eobLen) h3)

lemma bit1Inv_flush_bit1 (bw : BitWriter) (h : bit1Inv bw) :
    ∃ hsize : 0 < bw.flush.size, (bw.flush.get 0 hsize).toNat.testBit 1 = true := by
  classical
  cases h with
  | inl h0 =>
      rcases h0 with ⟨hout, hpos, _hlt8, hcur1⟩
      have h0' : bw.bitPos ≠ 0 := by omega
      have hflush : bw.flush = bw.out.push bw.cur := by
        simp [BitWriter.flush, h0']
      have hsize : 0 < bw.flush.size := by
        -- out.size = 0, so size is 1
        simp [hflush, ByteArray.size_push, hout]
      have hget' :
          (bw.out.push bw.cur)[0] = bw.cur := by
        simpa [hout] using (ByteArray.get_push_eq bw.out bw.cur)
      have hget : bw.flush.get 0 hsize = bw.cur := by
        simpa [hflush, byteArray_get_eq_getElem] using hget'
      exact ⟨hsize, by simpa [hget] using hcur1⟩
  | inr h0 =>
      rcases h0 with ⟨hsize0, hbit1⟩
      by_cases hzero : bw.bitPos = 0
      · have hflush : bw.flush = bw.out := by
          simp [BitWriter.flush, hzero]
        have hsize : 0 < bw.flush.size := by simpa [hflush] using hsize0
        have hget : bw.flush.get 0 hsize = bw.out.get 0 hsize0 := by
          simp [hflush]
        exact ⟨hsize, by simpa [hget] using hbit1⟩
      · have hflush : bw.flush = bw.out.push bw.cur := by
          simp [BitWriter.flush, hzero]
        have hsize : 0 < bw.flush.size := by
          simp [hflush, ByteArray.size_push]
        have hget' :
            (bw.out.push bw.cur)[0]'(by
                have : 0 < (bw.out.push bw.cur).size := by
                  simp [ByteArray.size_push]
                simp [ByteArray.size_push]) =
              bw.out[0]'hsize0 := by
          simpa [ByteArray.size_push] using
            (ByteArray.get_push_lt bw.out bw.cur 0 hsize0)
        have hget : bw.flush.get 0 hsize = bw.out.get 0 hsize0 := by
          simpa [hflush, byteArray_get_eq_getElem] using hget'
        exact ⟨hsize, by simpa [hget] using hbit1⟩

lemma deflateFixed_bit1 (raw : ByteArray) :
    ∃ h : 0 < (deflateFixed raw).size, ((deflateFixed raw).get 0 h).toNat.testBit 1 = true := by
  -- Use the bit1 invariant on the writer and translate to the flushed byte array.
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 1 2
  let bw3 := deflateFixedAux raw.data 0 bw2
  let eob := fixedLitLenCode 256
  let bw4 := bw3.writeBits (reverseBits eob.1 eob.2) eob.2
  have hinv : bit1Inv bw4 := by
    simpa [bw0, bw1, bw2, bw3, eob, bw4] using (bit1Inv_deflateFixed raw)
  rcases bit1Inv_flush_bit1 (bw := bw4) hinv with ⟨hsize, hbit⟩
  have hsize' : 0 < (deflateFixed raw).size := by
    simpa [deflateFixed, bw0, bw1, bw2, bw3, eob, bw4] using hsize
  refine ⟨hsize', ?_⟩
  simpa [deflateFixed, bw0, bw1, bw2, bw3, eob, bw4, byteArray_get_proof_irrel] using hbit

lemma deflateFixed_header_bit1 (raw : ByteArray) (h : 0 < (deflateFixed raw).size) :
    ((deflateFixed raw).get 0 h).toNat.testBit 1 = true := by
  rcases deflateFixed_bit1 raw with ⟨h0, hbit1⟩
  have hget :
      (deflateFixed raw).get 0 h = (deflateFixed raw).get 0 h0 := by
    exact byteArray_get_proof_irrel (a := deflateFixed raw) (i := 0) h h0
  simpa [hget] using hbit1

lemma inflateStoredAux_header_bit1_none (data : ByteArray) (h : 0 < data.size)
    (hbit1 : (data.get 0 h).toNat.testBit 1 = true) :
    inflateStoredAux data h = none := by
  let header := data.get 0 h
  have hbit :
      ((header.toNat >>> 1) &&& 1) = 1 := by
    have h := bitNat_of_testBit (x := header.toNat) (i := 1)
    calc
      ((header.toNat >>> 1) &&& 1) = (header.toNat.testBit 1).toNat := by
        simpa using h
      _ = 1 := by
        simpa [hbit1]
  have hmask : ((header.toNat >>> 1) &&& 3) ≠ 0 := by
    intro hzero
    have hmask1 :
        ((header.toNat >>> 1) &&& 1) = ((header.toNat >>> 1) &&& 3) &&& 1 := by
      symm
      calc
        ((header.toNat >>> 1) &&& 3) &&& 1
            = (header.toNat >>> 1) &&& (3 &&& 1) := by
                exact Nat.and_assoc _ _ _
        _ = (header.toNat >>> 1) &&& 1 := by
                simp
    have hbit0 : ((header.toNat >>> 1) &&& 1) = 0 := by
      calc
        ((header.toNat >>> 1) &&& 1)
            = ((header.toNat >>> 1) &&& 3) &&& 1 := hmask1
        _ = 0 := by
            simp [hzero]
    have hcontra : (0 : Nat) = 1 := by
      calc
        (0 : Nat) = ((header.toNat >>> 1) &&& 1) := by
          symm
          exact hbit0
        _ = 1 := hbit
    exact (Nat.zero_ne_one hcontra)
  have hbtype : ((header >>> 1) &&& (0x03 : UInt8)) ≠ 0 := by
    intro h0
    have h0' : (header.toNat >>> 1) &&& 3 = 0 := by
      have h0' := congrArg UInt8.toNat h0
      simpa [UInt8.toNat_and, UInt8.toNat_shiftRight] using h0'
    exact hmask h0'
  -- unfold and hit the btype check
  unfold inflateStoredAux
  simp [header, hbtype]

lemma inflateStoredAux_deflateFixed_none (raw : ByteArray) (h : 0 < (deflateFixed raw).size) :
    inflateStoredAux (deflateFixed raw) h = none := by
  have hbit1 := deflateFixed_header_bit1 raw h
  simpa using (inflateStoredAux_header_bit1_none (data := deflateFixed raw) h hbit1)

lemma inflateStored_deflateFixed_none (raw : ByteArray) :
    inflateStored (deflateFixed raw) = none := by
  by_cases h : 0 < (deflateFixed raw).size
  · have haux := inflateStoredAux_deflateFixed_none raw h
    simp [inflateStored, h, haux]
  · simp [inflateStored, h]


end Png
end Bitmaps
