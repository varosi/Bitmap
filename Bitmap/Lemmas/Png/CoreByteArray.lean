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
          _ = a[i] := by
            have hiA : i < a.size := by
              have hi' := hi
              simp at hi'
              exact hi'
            have h0iA : 0 + i < a.size := by
              simpa [Nat.zero_add] using hiA
            change a.get (0 + i) h0iA = a.get i hiA
            cases a with
            | mk data =>
                simp [ByteArray.get, Nat.zero_add] <;> rfl
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

/-- Two byte arrays are equal when their sizes and all in-bounds `get!` bytes
match. This packages the extensionality pattern used by PNG row proofs. -/
lemma byteArray_eq_of_size_get!
    (a b : ByteArray)
    (hsize : a.size = b.size)
    (hget : ∀ i, i < a.size → a.get! i = b.get! i) :
    a = b := by
  cases a with
  | mk adata =>
      cases b with
      | mk bdata =>
          simp [ByteArray.size] at hsize hget ⊢
          apply Array.ext
          · exact hsize
          · intro i hia hib
            have hget' := hget i (by simpa [ByteArray.size] using hia)
            have ha : adata[i]! = adata[i] := by
              exact getElem!_pos adata i hia
            have hb : bdata[i]! = bdata[i] := by
              exact getElem!_pos bdata i hib
            simpa [ByteArray.get!, ha, hb] using hget'

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
        change i < arr.size at h
        exact h
      calc
        arr[i]! = arr[i]'h' := by
          simp [getElem!_pos, h']
        _ = arr[i] := rfl

/-- Reading from an extracted byte slice with `get!` is the same as reading the
corresponding source byte when both indices are in bounds. -/
lemma byteArray_get!_extract
    (a : ByteArray) (start stop i : Nat)
    (hi : i < (a.extract start stop).size)
    (hsrc : start + i < a.size) :
    (a.extract start stop).get! i = a.get! (start + i) := by
  have hget :
      (a.extract start stop)[i]'hi = a[start + i]'hsrc := by
    exact ByteArray.get_extract (a := a) (start := start) (stop := stop) (i := i) hi
  calc
    (a.extract start stop).get! i = (a.extract start stop)[i]'hi := by
      simpa using byteArray_get!_eq_get (a := a.extract start stop) (i := i) hi
    _ = a[start + i]'hsrc := hget
    _ = a.get! (start + i) := by
      simpa using (byteArray_get!_eq_get (a := a) (i := start + i) hsrc).symm

/-- Reading before the appended byte of a `ByteArray.push` returns the original
byte. This is the `get!` form of `ByteArray.get_push_lt`. -/
lemma byteArray_get!_push_lt (a : ByteArray) (b : UInt8) (i : Nat)
    (hi : i < a.size) :
    (a.push b).get! i = a.get! i := by
  have hpush : i < (a.push b).size := by
    simpa [ByteArray.size_push] using Nat.lt_trans hi (Nat.lt_succ_self a.size)
  calc
    (a.push b).get! i = (a.push b)[i]'hpush := by
      simpa using byteArray_get!_eq_get (a := a.push b) (i := i) hpush
    _ = a[i]'hi := ByteArray.get_push_lt a b i hi
    _ = a.get! i := by
      simpa using (byteArray_get!_eq_get (a := a) (i := i) hi).symm

/-- Reading at the appended byte of a `ByteArray.push` returns that byte.
This is the `get!` form of `ByteArray.get_push_eq`. -/
lemma byteArray_get!_push_eq (a : ByteArray) (b : UInt8) :
    (a.push b).get! a.size = b := by
  have hpush : a.size < (a.push b).size := by
    simp [ByteArray.size_push]
  calc
    (a.push b).get! a.size = (a.push b)[a.size]'hpush := by
      simpa using byteArray_get!_eq_get (a := a.push b) (i := a.size) hpush
    _ = b := ByteArray.get_push_eq a b

/-- Extracting the original length after `push` returns the original array. -/
lemma byteArray_extract_push_prefix (a : ByteArray) (b : UInt8) :
    (a.push b).extract 0 a.size = a := by
  have hsize : ((a.push b).extract 0 a.size).size = a.size := by
    simp [ByteArray.size_extract]
  refine byteArray_eq_of_size_get! _ _ hsize ?_
  intro i hi
  have hiA : i < a.size := by
    simpa [hsize] using hi
  have hsrc : 0 + i < (a.push b).size := by
    simpa [ByteArray.size_push] using Nat.lt_trans hiA (Nat.lt_succ_self a.size)
  have hslice : i < ((a.push b).extract 0 a.size).size := by
    simpa [hsize] using hi
  calc
    ((a.push b).extract 0 a.size).get! i =
        (a.push b).get! (0 + i) :=
          byteArray_get!_extract (a.push b) 0 a.size i hslice hsrc
    _ = (a.push b).get! i := by simp
    _ = a.get! i := byteArray_get!_push_lt a b i hiA

/-- Extending a zero-based extract by one byte is the previous extract with
that next source byte appended. This is the prefix step used by row proofs. -/
lemma byteArray_extract_zero_succ_eq_push_get! (a : ByteArray) (n : Nat)
    (hn : n < a.size) :
    (a.extract 0 n).push (a.get! n) = a.extract 0 (n + 1) := by
  have hnle : n ≤ a.size := Nat.le_of_lt hn
  have hsucc : n + 1 ≤ a.size := Nat.succ_le_of_lt hn
  have hleftSize : (a.extract 0 n).size = n := by
    simp [ByteArray.size_extract, Nat.min_eq_left hnle]
  have hrightSize : (a.extract 0 (n + 1)).size = n + 1 := by
    simp [ByteArray.size_extract, Nat.min_eq_left hsucc]
  refine byteArray_eq_of_size_get! _ _ ?_ ?_
  · simp [ByteArray.size_push, hleftSize, hrightSize]
  · intro i hi
    have hiRight : i < (a.extract 0 (n + 1)).size := by
      simpa [ByteArray.size_push, hleftSize, hrightSize] using hi
    by_cases hin : i < n
    · have hiLeft : i < (a.extract 0 n).size := by
        simpa [hleftSize] using hin
      have hsrc : 0 + i < a.size := by
        simpa using Nat.lt_of_lt_of_le hin hnle
      calc
        ((a.extract 0 n).push (a.get! n)).get! i =
            (a.extract 0 n).get! i := by
              exact byteArray_get!_push_lt (a.extract 0 n) (a.get! n) i hiLeft
        _ = a.get! (0 + i) := byteArray_get!_extract a 0 n i hiLeft hsrc
        _ = (a.extract 0 (n + 1)).get! i := by
              exact (byteArray_get!_extract a 0 (n + 1) i hiRight hsrc).symm
    · have hieq : i = n := by
        have hi' : i < n + 1 := by
          simpa [ByteArray.size_push, hleftSize] using hi
        omega
      subst i
      have hsrc : 0 + n < a.size := by
        simpa using hn
      calc
        ((a.extract 0 n).push (a.get! n)).get! n =
            ((a.extract 0 n).push (a.get! n)).get! (a.extract 0 n).size := by
              simp [hleftSize]
        _ = a.get! n := byteArray_get!_push_eq (a.extract 0 n) (a.get! n)
        _ = a.get! (0 + n) := by simp
        _ = (a.extract 0 (n + 1)).get! n := by
              exact (byteArray_get!_extract a 0 (n + 1) n hiRight hsrc).symm

/-- Reading from the left side of an append with `get!` returns the same byte
as reading from the left array. -/
lemma byteArray_get!_append_left (a b : ByteArray) (i : Nat)
    (hi : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  have happ : i < (a ++ b).size := by
    simpa [ByteArray.size_append] using Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)
  calc
    (a ++ b).get! i = (a ++ b)[i]'happ := by
      simpa using byteArray_get!_eq_get (a := a ++ b) (i := i) happ
    _ = a[i]'hi := ByteArray.get_append_left (a := a) (b := b) (i := i) hi
    _ = a.get! i := by
      simpa using (byteArray_get!_eq_get (a := a) (i := i) hi).symm

/-- Any slice contained in a known zero-prefix can be read from that prefix.
This transfers row-block extracts from a final encoder buffer to its
accumulated raw prefix. -/
lemma byteArray_extract_slice_of_prefix (a pref : ByteArray) (n i j : Nat)
    (hprefix : a.extract 0 n = pref) (hj : j ≤ n) :
    a.extract i j = pref.extract i j := by
  have hslice :
      (a.extract 0 n).extract i j = a.extract i j := by
    simpa [Nat.min_eq_left hj] using
      (ByteArray.extract_extract (a := a) (i := 0) (j := n) (k := i) (l := j))
  calc
    a.extract i j = (a.extract 0 n).extract i j := hslice.symm
    _ = pref.extract i j := by rw [hprefix]

/-- A `get!` inside a known zero-prefix can be read from that prefix. -/
lemma byteArray_get!_of_prefix (a pref : ByteArray) (n i : Nat)
    (hprefix : a.extract 0 n = pref) (hi : i < pref.size) :
    a.get! i = pref.get! i := by
  have hslice : i < (a.extract 0 n).size := by
    simpa [hprefix] using hi
  have hsrc : 0 + i < a.size := by
    have hslice' := hslice
    simp [ByteArray.size_extract] at hslice'
    omega
  calc
    a.get! i = a.get! (0 + i) := by simp
    _ = (a.extract 0 n).get! i := by
          exact (byteArray_get!_extract a 0 n i hslice hsrc).symm
    _ = pref.get! i := by rw [hprefix]

/-- In a buffer shaped as `(a ++ b) ++ tail`, extracting exactly the middle
segment returns `b`. This is the row-payload layout fact for serialized
filtered PNG rows. -/
lemma byteArray_extract_append_middle_full (a b tail : ByteArray) :
    ((a ++ b) ++ tail).extract a.size (a.size + b.size) = b := by
  have h1 :
      ((a ++ b) ++ tail).extract a.size (a.size + b.size) =
        (b ++ tail).extract 0 b.size := by
    simpa [ByteArray.append_assoc] using
      (ByteArray.extract_append_size_add (a := a) (b := b ++ tail)
        (i := 0) (j := b.size))
  have h2 : (b ++ tail).extract 0 b.size = b := by
    simpa using
      (ByteArray.extract_append_eq_left (a := b) (b := tail) (i := b.size) rfl)
  rw [h1, h2]

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



end Png
end Bitmaps
