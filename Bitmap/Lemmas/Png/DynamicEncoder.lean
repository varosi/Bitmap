import Bitmap.Lemmas.Png.FixedBlockProofsCommon

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

/-- Zero repeats leave the byte stream unchanged. This is the base case for
distance-1 match expansion in the generated dynamic encoder. -/
@[simp] lemma pushByteRepeat_zero (out : ByteArray) (b : UInt8) :
    Png.pushByteRepeat out b 0 = out := rfl

/-- A successor repeat pushes one byte and continues. This exposes the recursive
shape used to prove distance-1 match expansion. -/
@[simp] lemma pushByteRepeat_succ (out : ByteArray) (b : UInt8) (n : Nat) :
    Png.pushByteRepeat out b (n + 1) =
      Png.pushByteRepeat (out.push b) b n := rfl

/-- Relates the generated dynamic encoder's repeat helper to the established
fixed-block proof helper, letting later proofs share repeat algebra. -/
lemma pushByteRepeat_eq_pushRepeat (out : ByteArray) (b : UInt8) (n : Nat) :
    Png.pushByteRepeat out b n = Png.pushRepeat out b n := by
  induction n generalizing out with
  | zero =>
      simp [Png.pushByteRepeat, Png.pushRepeat]
  | succ n ih =>
      simp [Png.pushByteRepeat, Png.pushRepeat, ih]

/-- Repeating a byte grows the stream by exactly the repeat count. This supports
token-expansion proofs that track output positions. -/
@[simp] lemma pushByteRepeat_size (out : ByteArray) (b : UInt8) (n : Nat) :
    (Png.pushByteRepeat out b n).size = out.size + n := by
  rw [pushByteRepeat_eq_pushRepeat]
  exact Png.pushRepeat_size out b n

/-- A repeated-byte expansion preserves nonemptiness of a nonempty prefix. This
is the condition needed for chained distance-1 match tokens. -/
lemma pushByteRepeat_pos (out : ByteArray) (b : UInt8) (n : Nat)
    (hout : 0 < out.size) :
    0 < (Png.pushByteRepeat out b n).size := by
  rw [pushByteRepeat_eq_pushRepeat]
  exact Png.pushRepeat_pos out b n hout

/-- Consecutive repeats of the same byte can be fused. This is the algebraic
step for proving expansion of chunked distance-1 runs. -/
lemma pushByteRepeat_append (out : ByteArray) (b : UInt8) (n m : Nat) :
    Png.pushByteRepeat (Png.pushByteRepeat out b n) b m =
      Png.pushByteRepeat out b (n + m) := by
  simp [pushByteRepeat_eq_pushRepeat, Png.pushRepeat_append]

/-- After a repeat, the last byte is the old last byte for zero repeats and the
repeated byte otherwise. This supports chained match expansion proofs. -/
lemma pushByteRepeat_last_get!
    (out : ByteArray) (b last : UInt8) (n : Nat)
    (hout : 0 < out.size)
    (hlast : out.get! (out.size - 1) = last) :
    (Png.pushByteRepeat out b n).get!
        ((Png.pushByteRepeat out b n).size - 1) =
      (if n = 0 then last else b) := by
  simpa [pushByteRepeat_eq_pushRepeat] using
    (Png.pushRepeat_last_get! out b last n hout hlast)

/-- A distance-1 match cannot expand an empty output. This isolates the invalid
match-prefix case before proving non-empty match expansion. -/
lemma deflateTokenExpand_matchDist1_empty (len : Nat) :
    Png.deflateTokenExpand ByteArray.empty (Png.DeflateToken.matchDist1 len) =
      ByteArray.empty := by
  simp [Png.deflateTokenExpand]

/-- A distance-1 match expands by repeating the previous byte. This is the local
payload-expansion fact needed before proving full token-stream expansion. -/
lemma deflateTokenExpand_matchDist1_of_pos (out : ByteArray) (len : Nat)
    (hout : 0 < out.size) :
    Png.deflateTokenExpand out (Png.DeflateToken.matchDist1 len) =
      Png.pushByteRepeat out (out.get! (out.size - 1)) len := by
  have hne : out.size ≠ 0 := Nat.ne_of_gt hout
  simp [Png.deflateTokenExpand, hne]

/-- Extends token-list expansion by one valid distance-1 match. The result
repeats the last expanded byte, matching the DEFLATE distance-1 semantics. -/
lemma deflateTokensExpand_push_matchDist1_of_pos
    (tokens : Array Png.DeflateToken) (len : Nat)
    (hout : 0 < (Png.deflateTokensExpand tokens).size) :
    Png.deflateTokensExpand (tokens.push (Png.DeflateToken.matchDist1 len)) =
      Png.pushByteRepeat (Png.deflateTokensExpand tokens)
        ((Png.deflateTokensExpand tokens).get!
          ((Png.deflateTokensExpand tokens).size - 1)) len := by
  simp only [Png.deflateTokensExpand, Array.foldl_push]
  exact deflateTokenExpand_matchDist1_of_pos _ _ hout

end Lemmas

end Bitmaps
