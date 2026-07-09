import Bitmap.Lemmas.Png.EncodeFilter
import Bitmap.Lemmas.Png.RowFilterSpec
import Bitmap.Lemmas.Png.CoreByteArray

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Row-filter inverse facts for indexed palette rows

Palette PNG rows use byte distance `1`.  These facts prove that the encoder's
fixed and adaptive row-filter choices reconstruct to the original row under the
decoder's `unfilterRow` implementation. -/

/-- A bounded natural survives conversion through `u8`.
This lets byte-filter proofs expose concrete filter-byte tags. -/
private lemma u8_toNat_of_lt (n : Nat) (h : n < 256) :
    (u8 n).toNat = n := by
  simpa [u8, UInt8.size] using
    UInt8.toNat_ofNat_of_lt' (n := n) (by simpa [UInt8.size] using h)

/-- Re-wrapping an existing byte's natural value with `u8` is identity.
This bridges byte-valued statements to the finite exhaustive proof below. -/
private lemma u8_toNat_eq_self (sample : UInt8) :
    u8 sample.toNat = sample := by
  simp [u8, UInt8.ofNat_toNat]

/-- A PNG filter residual plus the same predictor reconstructs the original
sample byte. This is the byte-level inverse used by row-filter proofs. -/
lemma filterResidualByte_inverse (sample predictor : UInt8) :
    u8 ((filterResidualByte sample predictor).toNat + predictor.toNat) = sample := by
  have h :
      ∀ sample predictor : Fin 256,
        u8 ((filterResidualByte (u8 sample.val) (u8 predictor.val)).toNat +
          (u8 predictor.val).toNat) = u8 sample.val := by
    native_decide
  simpa [u8_toNat_eq_self sample, u8_toNat_eq_self predictor] using
    h ⟨sample.toNat, by simpa using UInt8.toNat_lt sample⟩
      ⟨predictor.toNat, by simpa using UInt8.toNat_lt predictor⟩

/-- The residual inverse also works when the predictor is represented by a
bounded natural. Average and Paeth filters compute predictors this way. -/
private lemma filterResidualByte_inverse_nat
    (sample : UInt8) (predictor : Nat) (hpredictor : predictor < 256) :
    u8 ((filterResidualByte sample (u8 predictor)).toNat + predictor) = sample := by
  have hp : (u8 predictor).toNat = predictor := u8_toNat_of_lt predictor hpredictor
  simpa [hp] using filterResidualByte_inverse sample (u8 predictor)

/-- Paeth chooses one of its three byte-sized predictors.
The bound justifies applying the natural predictor inverse. -/
private lemma paethPredictor_lt_of_lt {a b c : Nat}
    (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    paethPredictor a b c < 256 := by
  let p : Int := (a : Int) + (b : Int) - (c : Int)
  let pa := Int.natAbs (p - a)
  let pb := Int.natAbs (p - b)
  let pc := Int.natAbs (p - c)
  change (if (decide (pa ≤ pb) && decide (pa ≤ pc)) = true then a
    else if pb ≤ pc then b else c) < 256
  by_cases hfirst : (decide (pa ≤ pb) && decide (pa ≤ pc)) = true
  · simp [hfirst, ha]
  · simp [hfirst]
    by_cases hsecond : pb ≤ pc
    · simp [hsecond, hb]
    · simp [hsecond, hc]

/-- Folding by pushing one byte for each range entry grows by the range length.
This is the size invariant behind indexed row-filter construction. -/
private lemma foldl_push_range_size
    (f : Nat → UInt8) (n : Nat) (out : ByteArray) :
    ((List.range n).foldl (fun out i => out.push (f i)) out).size =
      out.size + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [List.range_succ, List.foldl_append, ih, ByteArray.size_push,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Reading a byte pushed by a range fold returns the generator at that index.
This exposes each encoded filter residual for the inverse proof. -/
private lemma foldl_push_range_get!
    (f : Nat → UInt8) (n i : Nat) (hi : i < n) :
    ((List.range n).foldl (fun out j => out.push (f j)) ByteArray.empty).get! i =
      f i := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hfold :
          (List.range (n + 1)).foldl (fun out j => out.push (f j)) ByteArray.empty =
            ((List.range n).foldl (fun out j => out.push (f j)) ByteArray.empty).push
              (f n) := by
        simp [List.range_succ, List.foldl_append]
      rw [hfold]
      by_cases hin : i < n
      · have hsize :
            ((List.range n).foldl (fun out j => out.push (f j)) ByteArray.empty).size =
              n := by
          simpa using foldl_push_range_size f n ByteArray.empty
        rw [Png.byteArray_get!_push_lt _ _ _ (by simpa [hsize] using hin)]
        exact ih hin
      · have hieq : i = n := by omega
        subst i
        have hsize :
            ((List.range n).foldl (fun out j => out.push (f j)) ByteArray.empty).size =
              n := by
          simpa using foldl_push_range_size f n ByteArray.empty
        simpa [hsize] using
          Png.byteArray_get!_push_eq
            ((List.range n).foldl (fun out j => out.push (f j)) ByteArray.empty)
            (f n)

/-- A fixed filtered row stores exactly the residual byte selected by its
filter predictor. This is the encoder-side byte view. -/
private lemma filterRow_get! (filter : PngRowFilter) (row prev : ByteArray)
    (i : Nat) (hi : i < row.size) :
    (filterRow filter row prev 1).get! i =
      match filter with
      | .none => row.get! i
      | .sub =>
          filterResidualByte (row.get! i) (filterRowPredictor .sub row prev 1 i)
      | .up =>
          filterResidualByte (row.get! i) (filterRowPredictor .up row prev 1 i)
      | .average =>
          filterResidualByte (row.get! i) (filterRowPredictor .average row prev 1 i)
      | .paeth =>
          filterResidualByte (row.get! i) (filterRowPredictor .paeth row prev 1 i) := by
  cases filter <;>
    simp [filterRow, Std.Legacy.Range.forIn_eq_forIn_range',
      ← List.range_eq_range', foldl_push_range_get!, hi]

/-- Reconstructing a prefix of an encoded row returns the same prefix of the
source row. Induction over prefixes handles left-neighbor filters. -/
private lemma reconstruct_filterRow_prefix (filter : PngRowFilter)
    (row prev : ByteArray) (n : Nat) (hn : n ≤ row.size) :
    (List.range n).foldl
        (reconstructRowStep filter.toByte (filterRow filter row prev 1) prev 1)
        ByteArray.empty =
      row.extract 0 n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hnle : n ≤ row.size := Nat.le_of_succ_le hn
      have hlt : n < row.size := Nat.lt_of_succ_le hn
      have hfold :
          (List.range (n + 1)).foldl
              (reconstructRowStep filter.toByte (filterRow filter row prev 1) prev 1)
              ByteArray.empty =
            reconstructRowStep filter.toByte (filterRow filter row prev 1) prev 1
              (row.extract 0 n) n := by
        simp [List.range_succ, List.foldl_append, ih hnle]
      rw [hfold]
      have hleft :
          (if 1 ≤ n then (row.extract 0 n).get! (n - 1) else (0 : UInt8)) =
            if 1 ≤ n then row.get! (n - 1) else (0 : UInt8) := by
        by_cases h1 : 1 ≤ n
        · have hsize : (row.extract 0 n).size = n := by
            simp [ByteArray.size_extract, Nat.min_eq_left hnle]
          have hi : n - 1 < (row.extract 0 n).size := by
            simp [hsize]
            omega
          have hsrc : 0 + (n - 1) < row.size := by
            omega
          simp [h1, Png.byteArray_get!_extract row 0 n (n - 1) hi hsrc]
        · simp [h1]
      have hraw := filterRow_get! filter row prev n hlt
      have hpush := Png.byteArray_extract_zero_succ_eq_push_get! row n hlt
      rw [← hpush]
      unfold reconstructRowStep
      have hu0 : (u8 0 : UInt8).toNat = 0 := u8_toNat_of_lt 0 (by omega)
      have hu1 : (u8 1 : UInt8).toNat = 1 := u8_toNat_of_lt 1 (by omega)
      have hu2 : (u8 2 : UInt8).toNat = 2 := u8_toNat_of_lt 2 (by omega)
      have hu3 : (u8 3 : UInt8).toNat = 3 := u8_toNat_of_lt 3 (by omega)
      have hu4 : (u8 4 : UInt8).toNat = 4 := u8_toNat_of_lt 4 (by omega)
      cases filter with
      | none =>
          simp [PngRowFilter.toByte, hu0]
      | sub =>
          simp [PngRowFilter.toByte, filterRowPredictor, hraw, hleft,
            hu1, filterResidualByte_inverse]
      | up =>
          simp [PngRowFilter.toByte, filterRowPredictor, hraw, hu2,
            filterResidualByte_inverse]
      | average =>
          have havg_lt :
              (((if 1 ≤ n then row.get! (n - 1) else 0 : UInt8).toNat +
                  (if n < prev.size then prev.get! n else 0 : UInt8).toNat) / 2) < 256 := by
            have ha : (if 1 ≤ n then row.get! (n - 1) else 0 : UInt8).toNat < 256 :=
              UInt8.toNat_lt _
            have hb : (if n < prev.size then prev.get! n else 0 : UInt8).toNat < 256 :=
              UInt8.toNat_lt _
            omega
          have hinv :
              u8 ((filterResidualByte (row.get! n)
                    (u8 (((if 1 ≤ n then row.get! (n - 1) else 0 : UInt8).toNat +
                      (if n < prev.size then prev.get! n else 0 : UInt8).toNat) / 2))).toNat +
                    (((if 1 ≤ n then row.get! (n - 1) else 0 : UInt8).toNat +
                      (if n < prev.size then prev.get! n else 0 : UInt8).toNat) / 2)) =
                  row.get! n :=
            filterResidualByte_inverse_nat (row.get! n)
              (((if 1 ≤ n then row.get! (n - 1) else 0 : UInt8).toNat +
                (if n < prev.size then prev.get! n else 0 : UInt8).toNat) / 2) havg_lt
          simp [PngRowFilter.toByte, filterRowPredictor, hraw, hleft,
            hu3, hinv]
      | paeth =>
          have hpaeth_lt :
              paethPredictor
                  (if 1 ≤ n then row.get! (n - 1) else 0 : UInt8).toNat
                  (if n < prev.size then prev.get! n else 0 : UInt8).toNat
                  (if 1 ≤ n ∧ n < prev.size then prev.get! (n - 1) else 0 : UInt8).toNat <
                256 :=
            paethPredictor_lt_of_lt (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _)
          have hinv :
              u8 ((filterResidualByte (row.get! n)
                    (u8 (paethPredictor
                      (if 1 ≤ n then row.get! (n - 1) else 0 : UInt8).toNat
                      (if n < prev.size then prev.get! n else 0 : UInt8).toNat
                      (if 1 ≤ n ∧ n < prev.size then prev.get! (n - 1) else 0 : UInt8).toNat))).toNat +
                    paethPredictor
                      (if 1 ≤ n then row.get! (n - 1) else 0 : UInt8).toNat
                      (if n < prev.size then prev.get! n else 0 : UInt8).toNat
                      (if 1 ≤ n ∧ n < prev.size then prev.get! (n - 1) else 0 : UInt8).toNat) =
                  row.get! n :=
            filterResidualByte_inverse_nat (row.get! n)
              (paethPredictor
                (if 1 ≤ n then row.get! (n - 1) else 0 : UInt8).toNat
                (if n < prev.size then prev.get! n else 0 : UInt8).toNat
                (if 1 ≤ n ∧ n < prev.size then prev.get! (n - 1) else 0 : UInt8).toNat)
              hpaeth_lt
          simp [PngRowFilter.toByte, filterRowPredictor, hraw, hleft,
            hu4, hinv]

/-- Every fixed PNG row filter is inverted by the decoder's `unfilterRow` at
byte distance one. This packages the prefix proof at full row length. -/
private lemma unfilterRow_filterRow_fixed (filter : PngRowFilter)
    (row prev : ByteArray) :
    ∃ hfilter : filter.toByte.toNat ≤ 4,
      (if filter.toByte.toNat = 0 then filterRow filter row prev 1
       else unfilterRow filter.toByte (filterRow filter row prev 1) prev 1 hfilter) =
        row := by
  refine ⟨pngRowFilter_toByte_valid filter, ?_⟩
  cases filter with
  | none =>
      rfl
  | sub =>
      have hprefix := reconstruct_filterRow_prefix .sub row prev row.size le_rfl
      have hunfilter :=
        unfilterRow_eq_spec (PngRowFilter.sub.toByte) (filterRow .sub row prev 1) prev 1
          (pngRowFilter_toByte_valid .sub)
      have hprefixSpec :
          reconstructRowSpec PngRowFilter.sub.toByte (filterRow .sub row prev 1) prev 1 =
            row.extract 0 row.size := by
        have hfilterSize : (filterRow .sub row prev 1).size = row.size := by
          simpa using filterRow_size .sub row prev 1
        simpa [reconstructRowSpec, ← List.range_eq_range', hfilterSize] using hprefix
      have hu1 : (u8 1 : UInt8).toNat = 1 := u8_toNat_of_lt 1 (by omega)
      simpa [ByteArray.extract_zero_size, PngRowFilter.toByte, hu1] using
        hunfilter.trans hprefixSpec
  | up =>
      have hprefix := reconstruct_filterRow_prefix .up row prev row.size le_rfl
      have hunfilter :=
        unfilterRow_eq_spec (PngRowFilter.up.toByte) (filterRow .up row prev 1) prev 1
          (pngRowFilter_toByte_valid .up)
      have hprefixSpec :
          reconstructRowSpec PngRowFilter.up.toByte (filterRow .up row prev 1) prev 1 =
            row.extract 0 row.size := by
        have hfilterSize : (filterRow .up row prev 1).size = row.size := by
          simpa using filterRow_size .up row prev 1
        simpa [reconstructRowSpec, ← List.range_eq_range', hfilterSize] using hprefix
      have hu2 : (u8 2 : UInt8).toNat = 2 := u8_toNat_of_lt 2 (by omega)
      simpa [ByteArray.extract_zero_size, PngRowFilter.toByte, hu2] using
        hunfilter.trans hprefixSpec
  | average =>
      have hprefix := reconstruct_filterRow_prefix .average row prev row.size le_rfl
      have hunfilter :=
        unfilterRow_eq_spec (PngRowFilter.average.toByte) (filterRow .average row prev 1) prev 1
          (pngRowFilter_toByte_valid .average)
      have hprefixSpec :
          reconstructRowSpec PngRowFilter.average.toByte (filterRow .average row prev 1) prev 1 =
            row.extract 0 row.size := by
        have hfilterSize : (filterRow .average row prev 1).size = row.size := by
          simpa using filterRow_size .average row prev 1
        simpa [reconstructRowSpec, ← List.range_eq_range', hfilterSize] using hprefix
      have hu3 : (u8 3 : UInt8).toNat = 3 := u8_toNat_of_lt 3 (by omega)
      simpa [ByteArray.extract_zero_size, PngRowFilter.toByte, hu3] using
        hunfilter.trans hprefixSpec
  | paeth =>
      have hprefix := reconstruct_filterRow_prefix .paeth row prev row.size le_rfl
      have hunfilter :=
        unfilterRow_eq_spec (PngRowFilter.paeth.toByte) (filterRow .paeth row prev 1) prev 1
          (pngRowFilter_toByte_valid .paeth)
      have hprefixSpec :
          reconstructRowSpec PngRowFilter.paeth.toByte (filterRow .paeth row prev 1) prev 1 =
            row.extract 0 row.size := by
        have hfilterSize : (filterRow .paeth row prev 1).size = row.size := by
          simpa using filterRow_size .paeth row prev 1
        simpa [reconstructRowSpec, ← List.range_eq_range', hfilterSize] using hprefix
      have hu4 : (u8 4 : UInt8).toNat = 4 := u8_toNat_of_lt 4 (by omega)
      simpa [ByteArray.extract_zero_size, PngRowFilter.toByte, hu4] using
        hunfilter.trans hprefixSpec

private def rowFilterCandidateDecodes
    (candidate : PngRowFilter × ByteArray) (row prev : ByteArray) : Prop :=
  ∃ hfilter : candidate.1.toByte.toNat ≤ 4,
    (if candidate.1.toByte.toNat = 0 then candidate.2
     else unfilterRow candidate.1.toByte candidate.2 prev 1 hfilter) = row

/-- A fixed-filter adaptive candidate decodes to the original row.
This seeds the adaptive minimum-score preservation proof. -/
private lemma filterRow_candidate_decodes (filter : PngRowFilter)
    (row prev : ByteArray) :
    rowFilterCandidateDecodes (filter, filterRow filter row prev 1) row prev :=
  unfilterRow_filterRow_fixed filter row prev

/-- Choosing the lower-score adaptive candidate preserves the decode property.
Only the selected candidate changes, not its reconstruction proof. -/
private lemma chooseLowerFilterScore_decodes
    (best candidate : PngRowFilter × ByteArray) (row prev : ByteArray)
    (hbest : rowFilterCandidateDecodes best row prev)
    (hcandidate : rowFilterCandidateDecodes candidate row prev) :
    rowFilterCandidateDecodes (chooseLowerFilterScore best candidate) row prev := by
  unfold chooseLowerFilterScore
  by_cases hlt : filterRowScore candidate.2 < filterRowScore best.2
  · simpa [hlt] using hcandidate
  · simpa [hlt] using hbest

/-- Adaptive filtering returns one of the fixed candidates, each of which
decodes back to the original row. -/
private lemma adaptiveFilterRow_decodes (row prev : ByteArray) :
    rowFilterCandidateDecodes (adaptiveFilterRow row prev 1) row prev := by
  unfold adaptiveFilterRow
  apply chooseLowerFilterScore_decodes
  · apply chooseLowerFilterScore_decodes
    · apply chooseLowerFilterScore_decodes
      · apply chooseLowerFilterScore_decodes
        · exact filterRow_candidate_decodes .none row prev
        · exact filterRow_candidate_decodes .sub row prev
      · exact filterRow_candidate_decodes .up row prev
    · exact filterRow_candidate_decodes .average row prev
  · exact filterRow_candidate_decodes .paeth row prev

/-- Every public encoder filter strategy for byte-distance-one rows decodes
back to the original row. This is the row-level bridge from fixed/adaptive
filter selection to palette row reconstruction. -/
lemma filterRowForStrategy_decodes_one_byte_distance
    (strategy : PngFilterStrategy) (row prev : ByteArray) :
    let encoded := filterRowForStrategy strategy row prev 1
    ∃ hfilter : encoded.1.toNat ≤ 4,
      (if encoded.1.toNat = 0 then encoded.2
       else unfilterRow encoded.1 encoded.2 prev 1 hfilter) = row := by
  intro encoded
  cases strategy with
  | none =>
      refine ⟨by change (PngRowFilter.none.toByte).toNat ≤ 4; decide, ?_⟩
      rfl
  | fixed filter =>
      simpa [encoded, filterRowForStrategy] using unfilterRow_filterRow_fixed filter row prev
  | adaptive =>
      rcases adaptiveFilterRow_decodes row prev with ⟨hfilter, hdecode⟩
      refine ⟨hfilter, ?_⟩
      simpa [encoded, filterRowForStrategy] using hdecode

end Lemmas

end Bitmaps
