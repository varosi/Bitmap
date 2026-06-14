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

/-- Below three bytes, the dynamic token chunker emits no distance token. This
records the terminating branch used in run-expansion proofs. -/
lemma deflateMatchDist1Chunks_of_lt3 (tokens : Array Png.DeflateToken)
    (remaining : Nat) (h : ¬ 3 ≤ remaining) :
    Png.deflateMatchDist1Chunks tokens remaining = tokens := by
  rw [Png.deflateMatchDist1Chunks.eq_1]
  simp [h]

/-- At three or more bytes, the dynamic token chunker emits one distance-1
match chunk and recurses on the remaining length. -/
lemma deflateMatchDist1Chunks_of_ge3 (tokens : Array Png.DeflateToken)
    (remaining : Nat) (h : 3 ≤ remaining) :
    Png.deflateMatchDist1Chunks tokens remaining =
      Png.deflateMatchDist1Chunks
        (tokens.push (Png.DeflateToken.matchDist1
          (Png.chooseFixedMatchChunkLen remaining)))
        (remaining - Png.chooseFixedMatchChunkLen remaining) := by
  rw [Png.deflateMatchDist1Chunks.eq_1]
  simp [h]

/-- Zero literal repeats leave the token stream unchanged. This is the base case
for proving short-run token expansion. -/
@[simp] lemma pushLiteralRepeat_zero (tokens : Array Png.DeflateToken) (b : UInt8) :
    Png.pushLiteralRepeat tokens b 0 = tokens := rfl

/-- A successor literal repeat appends one literal token and continues. This
exposes the structural step used in short-run expansion proofs. -/
@[simp] lemma pushLiteralRepeat_succ
    (tokens : Array Png.DeflateToken) (b : UInt8) (n : Nat) :
    Png.pushLiteralRepeat tokens b (n + 1) =
      Png.pushLiteralRepeat (tokens.push (Png.DeflateToken.literal b)) b n := rfl

/-- A repeated-literal token sequence expands to the same byte repetition used
by existing fixed-block byte-stream proofs. -/
lemma deflateTokensExpand_pushLiteralRepeat_eq_pushRepeat
    (tokens : Array Png.DeflateToken) (b : UInt8) (n : Nat) :
    Png.deflateTokensExpand (Png.pushLiteralRepeat tokens b n) =
      Png.pushRepeat (Png.deflateTokensExpand tokens) b n := by
  induction n generalizing tokens with
  | zero =>
      simp [Png.pushLiteralRepeat, Png.pushRepeat]
  | succ n ih =>
      calc
        Png.deflateTokensExpand (Png.pushLiteralRepeat tokens b (n + 1)) =
          Png.deflateTokensExpand
            (Png.pushLiteralRepeat (tokens.push (Png.DeflateToken.literal b)) b n) := by
              rfl
        _ = Png.pushRepeat
              (Png.deflateTokensExpand (tokens.push (Png.DeflateToken.literal b))) b n := by
              exact ih (tokens.push (Png.DeflateToken.literal b))
        _ = Png.pushRepeat ((Png.deflateTokensExpand tokens).push b) b n := by
              simp [deflateTokensExpand_push_literal]
        _ = Png.pushRepeat (Png.deflateTokensExpand tokens) b (n + 1) := by
              exact Png.pushRepeat_push_eq (Png.deflateTokensExpand tokens) b n

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

/-- The generated dynamic run chunker expands to the same byte-stream model used
by the fixed-block distance-1 proofs. -/
lemma deflateTokensExpand_deflateMatchDist1Chunks_eq_dist1ChunkLoopOut
    (tokens : Array Png.DeflateToken) (remaining : Nat)
    (hout : 0 < (Png.deflateTokensExpand tokens).size) :
    Png.deflateTokensExpand (Png.deflateMatchDist1Chunks tokens remaining) =
      Png.dist1ChunkLoopOut (Png.deflateTokensExpand tokens) remaining := by
  induction remaining using Nat.strong_induction_on generalizing tokens with
  | h remaining ih =>
      by_cases hrem : 3 ≤ remaining
      · let chunk := Png.chooseFixedMatchChunkLen remaining
        have hstep :
            Png.deflateTokensExpand
                (tokens.push (Png.DeflateToken.matchDist1 chunk)) =
              Png.pushRepeat (Png.deflateTokensExpand tokens)
                ((Png.deflateTokensExpand tokens).get!
                  ((Png.deflateTokensExpand tokens).size - 1)) chunk := by
          calc
            Png.deflateTokensExpand
                (tokens.push (Png.DeflateToken.matchDist1 chunk)) =
              Png.pushByteRepeat (Png.deflateTokensExpand tokens)
                ((Png.deflateTokensExpand tokens).get!
                  ((Png.deflateTokensExpand tokens).size - 1)) chunk := by
                exact deflateTokensExpand_push_matchDist1_of_pos tokens chunk hout
            _ =
              Png.pushRepeat (Png.deflateTokensExpand tokens)
                ((Png.deflateTokensExpand tokens).get!
                  ((Png.deflateTokensExpand tokens).size - 1)) chunk := by
                rw [pushByteRepeat_eq_pushRepeat]
        have hout' :
            0 <
              (Png.deflateTokensExpand
                (tokens.push (Png.DeflateToken.matchDist1 chunk))).size := by
          rw [hstep]
          exact Png.pushRepeat_pos (Png.deflateTokensExpand tokens)
            ((Png.deflateTokensExpand tokens).get!
              ((Png.deflateTokensExpand tokens).size - 1)) chunk hout
        have hlt : remaining - chunk < remaining := by
          simpa [chunk] using Png.chooseFixedMatchChunkLen_sub_lt remaining hrem
        have hih :=
          ih (remaining - chunk) hlt
            (tokens.push (Png.DeflateToken.matchDist1 chunk)) hout'
        rw [deflateMatchDist1Chunks_of_ge3 tokens remaining hrem]
        rw [Png.dist1ChunkLoopOut_of_ge3 (Png.deflateTokensExpand tokens) remaining hrem]
        simpa [chunk, hstep] using hih
      · rw [deflateMatchDist1Chunks_of_lt3 tokens remaining hrem]
        rw [Png.dist1ChunkLoopOut_of_lt3 (Png.deflateTokensExpand tokens) remaining hrem]

/-- A generated dynamic long-run token sequence expands to the original repeated
bytes. This bridges literal-plus-distance tokens back to byte-stream semantics. -/
lemma deflateTokensExpand_longRun_eq_pushRepeat
    (tokens : Array Png.DeflateToken) (b : UInt8) (runLen : Nat)
    (h4 : 4 ≤ runLen) :
    Png.deflateTokensExpand
        (Png.deflateMatchDist1Chunks
          (tokens.push (Png.DeflateToken.literal b)) (runLen - 1)) =
      Png.pushRepeat (Png.deflateTokensExpand tokens) b runLen := by
  let out := Png.deflateTokensExpand tokens
  have hremGe : 3 ≤ runLen - 1 := by omega
  have houtLit :
      0 <
        (Png.deflateTokensExpand
          (tokens.push (Png.DeflateToken.literal b))).size := by
    simp [deflateTokensExpand_push_literal]
  have hbridge :=
    deflateTokensExpand_deflateMatchDist1Chunks_eq_dist1ChunkLoopOut
      (tokens.push (Png.DeflateToken.literal b)) (runLen - 1) houtLit
  have hloop :
      Png.dist1ChunkLoopOut (out.push b) (runLen - 1) =
        Png.pushRepeat (out.push b) b (runLen - 1) := by
    calc
      Png.dist1ChunkLoopOut (out.push b) (runLen - 1) =
          Png.pushRepeat (out.push b)
            ((out.push b).get! ((out.push b).size - 1))
            ((runLen - 1) - Png.dist1ChunkLoopRem (runLen - 1)) := by
              exact Png.dist1ChunkLoopOut_eq_pushRepeat (out.push b) (runLen - 1)
                (by simp [ByteArray.size_push])
      _ = Png.pushRepeat (out.push b) b (runLen - 1) := by
            have hlast : (out.push b).get! out.size = b := by
              simpa [ByteArray.size_push] using Png.get!_last_push out b
            have hrem0 : Png.dist1ChunkLoopRem (runLen - 1) = 0 :=
              Png.dist1ChunkLoopRem_eq_zero_of_ge3 (runLen - 1) hremGe
            simp [ByteArray.size_push, hlast, hrem0]
  calc
    Png.deflateTokensExpand
        (Png.deflateMatchDist1Chunks
          (tokens.push (Png.DeflateToken.literal b)) (runLen - 1)) =
      Png.dist1ChunkLoopOut
        (Png.deflateTokensExpand (tokens.push (Png.DeflateToken.literal b)))
        (runLen - 1) := hbridge
    _ = Png.dist1ChunkLoopOut (out.push b) (runLen - 1) := by
          simp [deflateTokensExpand_push_literal, out]
    _ = Png.pushRepeat (out.push b) b (runLen - 1) := hloop
    _ = Png.pushRepeat out b runLen := by
          have hrun : (runLen - 1) + 1 = runLen := by omega
          simpa [hrun] using Png.pushRepeat_push_eq out b (runLen - 1)

end Lemmas

end Bitmaps
