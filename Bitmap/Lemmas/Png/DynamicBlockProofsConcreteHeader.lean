import Bitmap.Lemmas.Png.DynamicBlockProofsReadTables

namespace Bitmaps

namespace Png

/-- Shows that the concrete code-length table literals really encode to the cached 30 payload bits. -/
lemma fixedWidthListBits_dynamicHeaderCodeLenLens :
    fixedWidthListBits 3 dynamicHeaderCodeLenLens = dynamicHeaderCodeLenLenBits := by
  native_decide

/-- Records the exact width of the ten 3-bit code-length table entries used by the dynamic header. -/
lemma dynamicHeaderCodeLenLens_width_eq :
    3 * dynamicHeaderCodeLenLens.length = 30 := by
  simpa [dynamicHeaderCodeLenLens_length]

/-- Rewrites the code-length table payload into the fixed header tail plus an arbitrary suffix. -/
lemma dynamicHeaderCodeLenLensBits_eq_tail_append (restBits : Nat) :
    dynamicHeaderCodeLenLensBits restBits =
      dynamicHeaderTailBits ||| (restBits <<< dynamicHeaderTailLen) := by
  rw [dynamicHeaderTailBits_eq_split, dynamicHeaderTailLen_eq_split]
  simp [dynamicHeaderCodeLenLensBits, dynamicHeaderCodeLenSymsRestBits,
    fixedWidthListBits_dynamicHeaderCodeLenLens, dynamicHeaderCodeLenLens_width_eq,
    dynamicHeaderCodeLenLen_eq, dynamicHeaderCodeLenSyms_length,
    Nat.shiftLeft_or_distrib, shiftLeft_shiftLeft, Nat.or_assoc,
    Nat.add_assoc, Nat.add_comm]

/-- Splits the code-length table bit count into the fixed tail length and the remaining suffix. -/
lemma dynamicHeaderCodeLenLensLen_eq_tail_append (restLen : Nat) :
    dynamicHeaderCodeLenLensLen restLen = dynamicHeaderTailLen + restLen := by
  rw [dynamicHeaderTailLen_eq_split]
  simp [dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen,
    dynamicHeaderCodeLenLens_width_eq, dynamicHeaderCodeLenLen_eq,
    dynamicHeaderCodeLenSyms_length]
  omega

/-- Gives the concrete 14-bit prefix value read from the dynamic block header. -/
lemma dynamicHeaderPrefixBits_eq :
    dynamicHeaderPrefixBits = 7167 := by
  decide

/-- Normalizes the prefix into the three header fields so later bit algebra stays readable. -/
lemma dynamicHeaderPrefixBits_or_parts_eq :
    31 ||| (992 ||| 6144) = dynamicHeaderPrefixBits := by
  decide

/-- Reassembles the full table-read bits from the fixed header table prefix plus a free suffix. -/
lemma dynamicHeaderReadBits_eq_table_append (restBits : Nat) :
    dynamicHeaderReadBits restBits =
      dynamicHeaderTableBits ||| (restBits <<< dynamicHeaderTableLen) := by
  unfold dynamicHeaderReadBits dynamicHeaderTableBits
  rw [dynamicHeaderCodeLenLensBits_eq_tail_append]
  have hcalc :
      (let bitsHclen := 6 ||| (dynamicHeaderTailBits ||| (restBits <<< dynamicHeaderTailLen)) <<< 4
       let bitsHdist := 31 ||| (bitsHclen <<< 5)
       31 ||| (bitsHdist <<< 5)) =
        31 ||| (992 ||| (6144 ||| (dynamicHeaderTailBits <<< 14 ||| restBits <<< 684))) := by
    simp [dynamicHeaderTailLen_eq_split, dynamicHeaderCodeLenLen_eq,
      dynamicHeaderCodeLenLens_width_eq, dynamicHeaderCodeLenSyms_length,
      Nat.shiftLeft_or_distrib, shiftLeft_shiftLeft, Nat.or_assoc, Nat.add_comm]
  rw [hcalc]
  calc
    31 ||| (992 ||| (6144 ||| (dynamicHeaderTailBits <<< 14 ||| restBits <<< 684))) =
        (31 ||| (992 ||| 6144)) ||| (dynamicHeaderTailBits <<< 14 ||| restBits <<< 684) := by
          rw [Nat.or_assoc, Nat.or_assoc]
    _ = dynamicHeaderPrefixBits ||| (dynamicHeaderTailBits <<< 14 ||| restBits <<< 684) := by
          rw [dynamicHeaderPrefixBits_or_parts_eq]
    _ = dynamicHeaderTableBits ||| (restBits <<< dynamicHeaderTableLen) := by
          simp [dynamicHeaderTableBits, dynamicHeaderPrefixBits, dynamicHeaderTableLen,
            dynamicHeaderPrefixLen, dynamicHeaderTailLen, Nat.or_assoc, Nat.add_comm]

/-- Bounds the fixed tail payload so `writeBits` can be split without overflow side conditions. -/
lemma dynamicHeaderTailBits_lt_pow :
    dynamicHeaderTailBits < 2 ^ dynamicHeaderTailLen := by
  native_decide

/-- Bounds the whole fixed table header payload by its declared bit width. -/
lemma dynamicHeaderTableBits_lt_pow :
    dynamicHeaderTableBits < 2 ^ dynamicHeaderTableLen := by
  native_decide

end Png

end Bitmaps
