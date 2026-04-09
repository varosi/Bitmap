import Bitmap.Lemmas.Png.DynamicBlockProofsReadTables

namespace Bitmaps

namespace Png

lemma fixedWidthListBits_dynamicHeaderCodeLenLens :
    fixedWidthListBits 3 dynamicHeaderCodeLenLens = dynamicHeaderCodeLenLenBits := by
  native_decide

lemma dynamicHeaderCodeLenLens_width_eq :
    3 * dynamicHeaderCodeLenLens.length = 30 := by
  simpa [dynamicHeaderCodeLenLens_length]

lemma dynamicHeaderCodeLenLensBits_eq_tail_append (restBits : Nat) :
    dynamicHeaderCodeLenLensBits restBits =
      dynamicHeaderTailBits ||| (restBits <<< dynamicHeaderTailLen) := by
  rw [dynamicHeaderTailBits_eq_split, dynamicHeaderTailLen_eq_split]
  simp [dynamicHeaderCodeLenLensBits, dynamicHeaderCodeLenSymsRestBits,
    fixedWidthListBits_dynamicHeaderCodeLenLens, dynamicHeaderCodeLenLens_width_eq,
    dynamicHeaderCodeLenLen_eq, dynamicHeaderCodeLenSyms_length,
    Nat.shiftLeft_or_distrib, shiftLeft_shiftLeft, Nat.or_assoc,
    Nat.add_assoc, Nat.add_comm]

lemma dynamicHeaderCodeLenLensLen_eq_tail_append (restLen : Nat) :
    dynamicHeaderCodeLenLensLen restLen = dynamicHeaderTailLen + restLen := by
  rw [dynamicHeaderTailLen_eq_split]
  simp [dynamicHeaderCodeLenLensLen, dynamicHeaderCodeLenSymsRestLen,
    dynamicHeaderCodeLenLens_width_eq, dynamicHeaderCodeLenLen_eq,
    dynamicHeaderCodeLenSyms_length, Nat.add_assoc, Nat.add_comm]

lemma dynamicHeaderPrefixBits_eq :
    dynamicHeaderPrefixBits = 7167 := by
  decide

lemma dynamicHeaderReadBits_eq_table_append (restBits : Nat) :
    dynamicHeaderReadBits restBits =
      dynamicHeaderTableBits ||| (restBits <<< dynamicHeaderTableLen) := by
  unfold dynamicHeaderReadBits dynamicHeaderTableBits
  rw [dynamicHeaderCodeLenLensBits_eq_tail_append]
  rw [dynamicHeaderPrefixBits_eq]
  simp [dynamicHeaderTableLen,
    dynamicHeaderPrefixBits, dynamicHeaderPrefixLen, dynamicHeaderTailLen,
    Nat.shiftLeft_or_distrib, shiftLeft_shiftLeft, Nat.or_assoc,
    Nat.add_comm]

lemma dynamicHeaderTailBits_lt_pow :
    dynamicHeaderTailBits < 2 ^ dynamicHeaderTailLen := by
  native_decide

lemma dynamicHeaderTableBits_lt_pow :
    dynamicHeaderTableBits < 2 ^ dynamicHeaderTableLen := by
  native_decide

end Png

end Bitmaps
