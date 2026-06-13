import Bitmap.Png

namespace Bitmaps

namespace Lemmas

/-- This checkpoint keeps public `.dynamic` on the existing proved encoder while
the generated dynamic encoder is proved incrementally. -/
lemma deflateDynamic_eq_deflateDynamicFast (raw : ByteArray) :
    Png.deflateDynamic raw = Png.deflateDynamicFast raw := rfl

/-- Base token-expansion fact for the generated encoder proof: a literal token
appends exactly its byte to the expanded output. -/
lemma deflateTokenExpand_literal (out : ByteArray) (b : UInt8) :
    Png.deflateTokenExpand out (Png.DeflateToken.literal b) = out.push b := rfl

/-- Base token-list expansion fact for the generated encoder proof: the empty
token stream expands to the empty byte stream. -/
lemma deflateTokensExpand_empty :
    Png.deflateTokensExpand #[] = ByteArray.empty := rfl

/-- Extends token-list expansion by one literal. This is the induction step
needed when a tokenizer branch emits an ordinary byte. -/
lemma deflateTokensExpand_push_literal (tokens : Array Png.DeflateToken) (b : UInt8) :
    Png.deflateTokensExpand (tokens.push (Png.DeflateToken.literal b)) =
      (Png.deflateTokensExpand tokens).push b := by
  simp [Png.deflateTokensExpand, Png.deflateTokenExpand]

/-- A distance-1 match cannot expand an empty output. This isolates the invalid
match-prefix case before proving non-empty match expansion. -/
lemma deflateTokenExpand_matchDist1_empty (len : Nat) :
    Png.deflateTokenExpand ByteArray.empty (Png.DeflateToken.matchDist1 len) =
      ByteArray.empty := by
  simp [Png.deflateTokenExpand]

end Lemmas

end Bitmaps
