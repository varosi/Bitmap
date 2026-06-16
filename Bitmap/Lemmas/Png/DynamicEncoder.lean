import Bitmap.Lemmas.Png.FixedBlockProofsRunEncode

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

/-- Match-token validity predicate for the generated dynamic encoder. It keeps
the token IR connected to DEFLATE's legal match-length interval. -/
def DeflateTokensMatchLengthsValid (tokens : Array Png.DeflateToken) : Prop :=
  ∀ target len (htarget : target < tokens.size),
    tokens[target]'htarget = Png.DeflateToken.matchDist1 len →
      3 ≤ len ∧ len ≤ 258

/-- The empty token stream has no invalid match lengths. This is the top-level
base case for tokenizer validity. -/
lemma deflateTokensMatchLengthsValid_empty :
    DeflateTokensMatchLengthsValid #[] := by
  intro target len htarget _
  simp at htarget

/-- Adding a literal token preserves validity of all existing match lengths.
This isolates the literal branch of the tokenizer. -/
lemma deflateTokensMatchLengthsValid_push_literal
    (tokens : Array Png.DeflateToken) (b : UInt8)
    (hvalid : DeflateTokensMatchLengthsValid tokens) :
    DeflateTokensMatchLengthsValid
      (tokens.push (Png.DeflateToken.literal b)) := by
  intro target len htarget ht
  by_cases hlt : target < tokens.size
  · have hget :
        (tokens.push (Png.DeflateToken.literal b))[target] = tokens[target] := by
      exact Array.getElem_push_lt hlt
    exact hvalid target len hlt (by simpa [hget] using ht)
  · have heq : target = tokens.size := by
      have hsize := Array.size_push (xs := tokens) (v := Png.DeflateToken.literal b)
      omega
    subst target
    have hget :
        (tokens.push (Png.DeflateToken.literal b))[tokens.size] =
          Png.DeflateToken.literal b :=
      Array.getElem_push_eq
    simp [hget] at ht

/-- Adding one legal distance-1 match preserves token validity. This packages
the array-push split used by generated chunk proofs. -/
lemma deflateTokensMatchLengthsValid_push_matchDist1
    (tokens : Array Png.DeflateToken) (chunk : Nat)
    (hchunk : 3 ≤ chunk ∧ chunk ≤ 258)
    (hvalid : DeflateTokensMatchLengthsValid tokens) :
    DeflateTokensMatchLengthsValid
      (tokens.push (Png.DeflateToken.matchDist1 chunk)) := by
  intro target len htarget ht
  by_cases hlt : target < tokens.size
  · have hget :
        (tokens.push (Png.DeflateToken.matchDist1 chunk))[target] =
          tokens[target] := by
      exact Array.getElem_push_lt hlt
    exact hvalid target len hlt (by simpa [hget] using ht)
  · have heq : target = tokens.size := by
      have hsize := Array.size_push (xs := tokens) (v := Png.DeflateToken.matchDist1 chunk)
      omega
    subst target
    have hget :
        (tokens.push (Png.DeflateToken.matchDist1 chunk))[tokens.size] =
          Png.DeflateToken.matchDist1 chunk :=
      Array.getElem_push_eq
    have hmatch :
        Png.DeflateToken.matchDist1 chunk =
          Png.DeflateToken.matchDist1 len := by
      simpa [hget] using ht
    cases hmatch
    exact hchunk

/-- The match chunker only appends legal DEFLATE match lengths. This lets later
payload proofs reuse the existing fixed-block chunk bounds. -/
lemma deflateMatchDist1Chunks_matchLengthsValid
    (tokens : Array Png.DeflateToken) (remaining : Nat)
    (hvalid : DeflateTokensMatchLengthsValid tokens) :
    DeflateTokensMatchLengthsValid
      (Png.deflateMatchDist1Chunks tokens remaining) := by
  induction remaining using Nat.strong_induction_on generalizing tokens with
  | h remaining ih =>
      by_cases hrem : 3 ≤ remaining
      · let chunk := Png.chooseFixedMatchChunkLen remaining
        have hchunk : 3 ≤ chunk ∧ chunk ≤ 258 := by
          have hbounds := Png.chooseFixedMatchChunkLen_bounds remaining hrem
          exact ⟨hbounds.1, hbounds.2.1⟩
        have hnext :
            DeflateTokensMatchLengthsValid
              (tokens.push (Png.DeflateToken.matchDist1 chunk)) :=
          deflateTokensMatchLengthsValid_push_matchDist1 tokens chunk hchunk hvalid
        have hlt : remaining - chunk < remaining := by
          simpa [chunk] using Png.chooseFixedMatchChunkLen_sub_lt remaining hrem
        have hih :=
          ih (remaining - chunk) hlt
            (tokens.push (Png.DeflateToken.matchDist1 chunk)) hnext
        rw [deflateMatchDist1Chunks_of_ge3 tokens remaining hrem]
        simpa [chunk] using hih
      · rw [deflateMatchDist1Chunks_of_lt3 tokens remaining hrem]
        exact hvalid

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

/-- Repeating literals preserves match-length validity because it appends no
match tokens. This covers the tokenizer's short-run branch. -/
lemma pushLiteralRepeat_matchLengthsValid
    (tokens : Array Png.DeflateToken) (b : UInt8) (n : Nat)
    (hvalid : DeflateTokensMatchLengthsValid tokens) :
    DeflateTokensMatchLengthsValid (Png.pushLiteralRepeat tokens b n) := by
  induction n generalizing tokens with
  | zero =>
      simpa using hvalid
  | succ n ih =>
      exact ih (tokens.push (Png.DeflateToken.literal b))
        (deflateTokensMatchLengthsValid_push_literal tokens b hvalid)

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

/-- Expanding the full generated dynamic tokenizer reconstructs the input bytes
from the current array index. This is the tokenizer-level correctness bridge. -/
lemma deflateTokensExpand_deflateTokensDist1Aux_eq_byteArrayFromArray
    (data : Array UInt8) (i : Nat) (tokens : Array Png.DeflateToken) :
    Png.deflateTokensExpand (Png.deflateTokensDist1Aux data i tokens) =
      Png.byteArrayFromArray data i (Png.deflateTokensExpand tokens) := by
  classical
  by_cases hlt : i < data.size
  · let b := data[i]
    let j := Png.sameByteRunEndFast data b (i + 1)
    let runLen := j - i
    let out := Png.deflateTokensExpand tokens
    let tokens' :=
      if 4 ≤ runLen then
        Png.deflateMatchDist1Chunks (tokens.push (Png.DeflateToken.literal b)) (runLen - 1)
      else
        Png.pushLiteralRepeat tokens b runLen
    have hsame : j = Png.sameByteRunEnd data b (i + 1) := by
      simpa [j] using sameByteRunEndFast_eq_sameByteRunEnd data b (i + 1)
    have hscan0 : Png.sameByteRunEnd data b i = Png.sameByteRunEnd data b (i + 1) := by
      rw [Png.sameByteRunEnd.eq_def]
      simp [hlt, b]
    have hrunScan : Png.sameByteRunEnd data b i - i = runLen := by
      calc
        Png.sameByteRunEnd data b i - i =
            Png.sameByteRunEnd data b (i + 1) - i := by simp [hscan0]
        _ = j - i := by simp [hsame]
        _ = runLen := by simp [runLen]
    have hbaRun :
        Png.byteArrayFromArray data i out =
          Png.byteArrayFromArray data j (Png.pushRepeat out b runLen) := by
      have htmp := Png.byteArrayFromArray_sameByteRunEnd_pushRepeat data b i out
      calc
        Png.byteArrayFromArray data i out =
            Png.byteArrayFromArray data (Png.sameByteRunEnd data b i)
              (Png.pushRepeat out b (Png.sameByteRunEnd data b i - i)) := htmp
        _ = Png.byteArrayFromArray data (Png.sameByteRunEnd data b (i + 1))
              (Png.pushRepeat out b (Png.sameByteRunEnd data b i - i)) := by
                simp [hscan0]
        _ = Png.byteArrayFromArray data j
              (Png.pushRepeat out b (Png.sameByteRunEnd data b i - i)) := by
                simp [hsame]
        _ = Png.byteArrayFromArray data j (Png.pushRepeat out b runLen) := by
              simp [hrunScan]
    have hacc :
        Png.deflateTokensExpand tokens' = Png.pushRepeat out b runLen := by
      by_cases h4 : 4 ≤ runLen
      · simp [tokens', h4, out, deflateTokensExpand_longRun_eq_pushRepeat]
      · simp [tokens', h4, out, deflateTokensExpand_pushLiteralRepeat_eq_pushRepeat]
    have hih :
        Png.deflateTokensExpand (Png.deflateTokensDist1Aux data j tokens') =
          Png.byteArrayFromArray data j (Png.deflateTokensExpand tokens') :=
      deflateTokensExpand_deflateTokensDist1Aux_eq_byteArrayFromArray data j tokens'
    have hstep :
        Png.deflateTokensExpand (Png.deflateTokensDist1Aux data i tokens) =
          Png.deflateTokensExpand (Png.deflateTokensDist1Aux data j tokens') := by
      rw [Png.deflateTokensDist1Aux.eq_1]
      simp [hlt, b, j, runLen, tokens']
    calc
      Png.deflateTokensExpand (Png.deflateTokensDist1Aux data i tokens) =
          Png.deflateTokensExpand (Png.deflateTokensDist1Aux data j tokens') := hstep
      _ = Png.byteArrayFromArray data j (Png.deflateTokensExpand tokens') := hih
      _ = Png.byteArrayFromArray data j (Png.pushRepeat out b runLen) := by simp [hacc]
      _ = Png.byteArrayFromArray data i out := hbaRun.symm
      _ = Png.byteArrayFromArray data i (Png.deflateTokensExpand tokens) := by simp [out]
  · rw [Png.deflateTokensDist1Aux.eq_1]
    rw [Png.byteArrayFromArray_unfold]
    simp [hlt]
termination_by data.size - i
decreasing_by
  have hgt : i < Png.sameByteRunEndFast data data[i] (i + 1) := by
    exact sameByteRunEndFast_gt_prev data i hlt
  have hle : Png.sameByteRunEndFast data data[i] (i + 1) ≤ data.size := by
    exact sameByteRunEndFast_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  exact (by omega :
    data.size - Png.sameByteRunEndFast data data[i] (i + 1) < data.size - i)

/-- The public generated dynamic tokenizer expands exactly to its source bytes.
This is the top-level tokenizer correctness statement for the new encoder. -/
lemma deflateTokensExpand_deflateTokensDist1 (raw : ByteArray) :
    Png.deflateTokensExpand (Png.deflateTokensDist1 raw) = raw := by
  calc
    Png.deflateTokensExpand (Png.deflateTokensDist1 raw) =
        Png.byteArrayFromArray raw.data 0 ByteArray.empty := by
          simpa [Png.deflateTokensDist1, deflateTokensExpand_empty] using
            deflateTokensExpand_deflateTokensDist1Aux_eq_byteArrayFromArray raw.data 0 #[]
    _ = raw := by
          simpa using Png.byteArrayFromArray_empty (data := raw.data)

/-- The generated tokenizer preserves legal match lengths from any valid token
prefix. This is the recursive bridge from byte scanning to payload safety. -/
lemma deflateTokensDist1Aux_matchLengthsValid
    (data : Array UInt8) (i : Nat) (tokens : Array Png.DeflateToken)
    (hvalid : DeflateTokensMatchLengthsValid tokens) :
    DeflateTokensMatchLengthsValid
      (Png.deflateTokensDist1Aux data i tokens) := by
  rw [Png.deflateTokensDist1Aux.eq_1]
  by_cases hlt : i < data.size
  · let b := data[i]
    let j := Png.sameByteRunEndFast data b (i + 1)
    let runLen := j - i
    let tokens' :=
      if 4 ≤ runLen then
        Png.deflateMatchDist1Chunks (tokens.push (Png.DeflateToken.literal b)) (runLen - 1)
      else
        Png.pushLiteralRepeat tokens b runLen
    have htokens' : DeflateTokensMatchLengthsValid tokens' := by
      by_cases h4 : 4 ≤ runLen
      · have hpush :
            DeflateTokensMatchLengthsValid
              (tokens.push (Png.DeflateToken.literal b)) :=
          deflateTokensMatchLengthsValid_push_literal tokens b hvalid
        have hchunks :=
          deflateMatchDist1Chunks_matchLengthsValid
            (tokens.push (Png.DeflateToken.literal b)) (runLen - 1) hpush
        simpa [tokens', h4] using hchunks
      · have hlits :=
          pushLiteralRepeat_matchLengthsValid tokens b runLen hvalid
        simpa [tokens', h4] using hlits
    have hrec :=
      deflateTokensDist1Aux_matchLengthsValid data j tokens' htokens'
    simpa [hlt, b, j, runLen, tokens'] using hrec
  · simp [hlt, hvalid]
termination_by data.size - i
decreasing_by
  have hgt : i < Png.sameByteRunEndFast data data[i] (i + 1) := by
    exact sameByteRunEndFast_gt_prev data i hlt
  have hle : Png.sameByteRunEndFast data data[i] (i + 1) ≤ data.size := by
    exact sameByteRunEndFast_le_size data data[i] (i + 1) (Nat.succ_le_of_lt hlt)
  exact (by omega :
    data.size - Png.sameByteRunEndFast data data[i] (i + 1) < data.size - i)

/-- Every match token emitted by the public generated dynamic tokenizer has a
DEFLATE-valid match length. This prepares generated payload decode proofs. -/
lemma deflateTokensDist1_matchLengthsValid (raw : ByteArray) :
    DeflateTokensMatchLengthsValid (Png.deflateTokensDist1 raw) := by
  simpa [Png.deflateTokensDist1] using
    deflateTokensDist1Aux_matchLengthsValid raw.data 0 #[]
      deflateTokensMatchLengthsValid_empty

/-- Indexed match tokens from the public generated tokenizer have legal DEFLATE
lengths. This is the convenient payload-proof form of tokenizer validity. -/
lemma deflateTokensDist1_match_len_bounds_at
    (raw : ByteArray) (target len : Nat)
    (htarget : target < (Png.deflateTokensDist1 raw).size)
    (ht : (Png.deflateTokensDist1 raw)[target]'htarget =
      Png.DeflateToken.matchDist1 len) :
    3 ≤ len ∧ len ≤ 258 :=
  deflateTokensDist1_matchLengthsValid raw target len htarget ht

/-- Incrementing one frequency slot preserves the table shape. This is the base
size invariant for generated dynamic Huffman frequency tables. -/
@[simp] lemma incrementNatAt_size (arr : Array Nat) (idx : Nat) :
    (Png.incrementNatAt arr idx).size = arr.size := by
  simp [Png.incrementNatAt]

/-- Incrementing an in-bounds frequency slot makes that slot positive. This is
used to show generated tables contain required symbols such as EOB. -/
lemma incrementNatAt_get!_pos (arr : Array Nat) (idx : Nat)
    (hidx : idx < arr.size) :
    0 < (Png.incrementNatAt arr idx)[idx]! := by
  simp [Png.incrementNatAt, hidx]

/-- A positive `get!` result proves the index is in bounds. This turns
availability facts into ordinary bounded array facts. -/
lemma get!_pos_implies_inBounds (arr : Array Nat) (idx : Nat)
    (hpos : 0 < arr[idx]!) :
    idx < arr.size := by
  by_cases hidx : idx < arr.size
  · exact hidx
  · simp [hidx] at hpos

/-- Reading the index just written by `Array.set!` returns the written value.
This packages the core `Array.set` lemma for `get!`-based encoder proofs. -/
lemma getElem!_set!_eq {α : Type} [Inhabited α]
    (arr : Array α) (idx : Nat) (v : α)
    (hidx : idx < arr.size) :
    (arr.set! idx v)[idx]! = v := by
  unfold Array.set!
  simp [Array.setIfInBounds, hidx]

/-- Writing a different index with `Array.set!` preserves this `get!` result.
This keeps later recursive table-filling proofs focused on the target symbol. -/
lemma getElem!_set!_ne {α : Type} [Inhabited α]
    (arr : Array α) (idx target : Nat) (v : α)
    (htarget : target < arr.size)
    (hne : idx ≠ target) :
    (arr.set! idx v)[target]! = arr[target]! := by
  unfold Array.set!
  by_cases hidx : idx < arr.size
  · let arr' := arr.set idx v hidx
    have htarget' : target < arr'.size := by
      simp [arr', htarget]
    simp [Array.setIfInBounds, hidx]
    rw [getElem!_pos arr' target htarget']
    rw [getElem!_pos arr target htarget]
    simpa [arr'] using
      (Array.getElem_set_ne (xs := arr) (i := idx) hidx
        (v := v) (j := target) htarget hne)
  · simp [Array.setIfInBounds, hidx]

/-- Incrementing a different frequency slot preserves this target slot. This
keeps count-table proofs focused on the one bucket that can change. -/
lemma incrementNatAt_get!_ne
    (arr : Array Nat) (idx target : Nat)
    (htarget : target < arr.size)
    (hne : idx ≠ target) :
    (Png.incrementNatAt arr idx)[target]! = arr[target]! := by
  unfold Png.incrementNatAt
  exact getElem!_set!_ne arr idx target (arr[idx]! + 1) htarget hne

/-- Incrementing one frequency slot can increase any fixed target bucket by at
most one. This is the local counting bound for canonical table proofs. -/
lemma incrementNatAt_get!_le_succ
    (arr : Array Nat) (idx target : Nat)
    (htarget : target < arr.size) :
    (Png.incrementNatAt arr idx)[target]! ≤ arr[target]! + 1 := by
  by_cases heq : idx = target
  · subst target
    simp [Png.incrementNatAt, htarget]
  · rw [incrementNatAt_get!_ne arr idx target htarget heq]
    omega

/-- Incrementing any frequency slot preserves an already-positive slot. This is
the scanner invariant used by generated payload-availability proofs. -/
lemma incrementNatAt_get!_pos_of_pos
    (arr : Array Nat) (idx sym : Nat)
    (hpos : 0 < arr[sym]!) :
    0 < (Png.incrementNatAt arr idx)[sym]! := by
  have hsym : sym < arr.size := get!_pos_implies_inBounds arr sym hpos
  have hposElem : 0 < arr[sym] := by
    simpa [getElem!_pos arr sym hsym] using hpos
  unfold Png.incrementNatAt
  unfold Array.set!
  by_cases hidx : idx < arr.size
  · simp [Array.setIfInBounds, hidx]
    let arr' := arr.set idx (arr[idx] + 1) hidx
    have hsym' : sym < arr'.size := by simp [arr', hsym]
    have hget :
        arr'[sym] = if idx = sym then arr[idx] + 1 else arr[sym] := by
      simpa [arr'] using
        Array.getElem_set (xs := arr) (i := idx) hidx
          (v := arr[idx] + 1) (j := sym) hsym'
    change 0 < arr'[sym]!
    rw [getElem!_pos arr' sym hsym']
    by_cases heq : idx = sym
    · subst heq
      simp [hget]
    · simp [hget, heq]
      exact hposElem
  · simp [Array.setIfInBounds, hidx, hpos]

/-- A positive first array slot implies the first slot is in bounds. This lets
frequency-preservation proofs reuse in-bounds increment lemmas. -/
lemma get!_zero_pos_implies_size_pos (arr : Array Nat)
    (hpos : 0 < arr[0]!) :
    0 < arr.size := by
  exact get!_pos_implies_inBounds arr 0 hpos

/-- Literal/length frequency accumulation preserves whatever table shape it is
given. The final table-size theorem instantiates this with the DEFLATE size. -/
lemma litLenSymbolFreqsAux_size
    (tokens : Array Png.DeflateToken) (i : Nat) (freqs : Array Nat) :
    (Png.litLenSymbolFreqsAux tokens i freqs).size = freqs.size := by
  rw [Png.litLenSymbolFreqsAux.eq_1]
  by_cases h : i < tokens.size
  · cases ht : tokens[i]'h with
    | literal b =>
        have hrec :=
          litLenSymbolFreqsAux_size tokens (i + 1) (Png.incrementNatAt freqs b.toNat)
        simp [h, ht, hrec]
    | matchDist1 len =>
        let sym := (Png.fixedLenMatchInfo len).1
        have hrec :=
          litLenSymbolFreqsAux_size tokens (i + 1) (Png.incrementNatAt freqs sym)
        simpa [h, ht, sym] using hrec
  · simp [h]
termination_by tokens.size - i
decreasing_by
  all_goals
    have hlt : i < tokens.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1) hlt (Nat.lt_succ_self i)

/-- Literal/length frequency collection keeps the DEFLATE literal table size.
This is needed before proving generated `HLIT` and literal payload lookup. -/
lemma litLenSymbolFreqs_size (tokens : Array Png.DeflateToken) :
    (Png.litLenSymbolFreqs tokens).size = 286 := by
  simp [Png.litLenSymbolFreqs, litLenSymbolFreqsAux_size]

/-- Once a literal/length frequency is positive, the rest of the scan preserves
that fact. Later payload proofs use this across preceding tokens. -/
lemma litLenSymbolFreqsAux_pos_of_pos
    (tokens : Array Png.DeflateToken) (i : Nat) (freqs : Array Nat) (sym : Nat)
    (hpos : 0 < freqs[sym]!) :
    0 < (Png.litLenSymbolFreqsAux tokens i freqs)[sym]! := by
  rw [Png.litLenSymbolFreqsAux.eq_1]
  by_cases h : i < tokens.size
  · cases ht : tokens[i]'h with
    | literal b =>
        have hinc :
            0 < (Png.incrementNatAt freqs b.toNat)[sym]! :=
          incrementNatAt_get!_pos_of_pos freqs b.toNat sym hpos
        have hrec :=
          litLenSymbolFreqsAux_pos_of_pos tokens (i + 1)
            (Png.incrementNatAt freqs b.toNat) sym hinc
        simpa [h, ht] using hrec
    | matchDist1 len =>
        let matchSym := (Png.fixedLenMatchInfo len).1
        have hinc :
            0 < (Png.incrementNatAt freqs matchSym)[sym]! :=
          incrementNatAt_get!_pos_of_pos freqs matchSym sym hpos
        have hrec :=
          litLenSymbolFreqsAux_pos_of_pos tokens (i + 1)
            (Png.incrementNatAt freqs matchSym) sym hinc
        simpa [h, ht, matchSym] using hrec
  · simp [h, hpos]
termination_by tokens.size - i
decreasing_by
  all_goals
    have hlt : i < tokens.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- If the current token is a literal, scanning from that token gives its
literal/length symbol a positive frequency. -/
lemma litLenSymbolFreqsAux_literal_pos_of_current
    (tokens : Array Png.DeflateToken) (i : Nat) (freqs : Array Nat) (b : UInt8)
    (h : i < tokens.size)
    (ht : tokens[i]'h = Png.DeflateToken.literal b)
    (hidx : b.toNat < freqs.size) :
    0 < (Png.litLenSymbolFreqsAux tokens i freqs)[b.toNat]! := by
  rw [Png.litLenSymbolFreqsAux.eq_1]
  have hinc :
      0 < (Png.incrementNatAt freqs b.toNat)[b.toNat]! :=
    incrementNatAt_get!_pos freqs b.toNat hidx
  have hrec :=
    litLenSymbolFreqsAux_pos_of_pos tokens (i + 1)
      (Png.incrementNatAt freqs b.toNat) b.toNat hinc
  simpa [h, ht] using hrec

/-- If the current token is a distance-1 match, scanning from that token gives
its literal/length match symbol a positive frequency. -/
lemma litLenSymbolFreqsAux_match_pos_of_current
    (tokens : Array Png.DeflateToken) (i : Nat) (freqs : Array Nat) (len : Nat)
    (h : i < tokens.size)
    (ht : tokens[i]'h = Png.DeflateToken.matchDist1 len)
    (hidx : (Png.fixedLenMatchInfo len).1 < freqs.size) :
    0 <
      (Png.litLenSymbolFreqsAux tokens i freqs)[(Png.fixedLenMatchInfo len).1]! := by
  rw [Png.litLenSymbolFreqsAux.eq_1]
  let matchSym := (Png.fixedLenMatchInfo len).1
  have hinc :
      0 < (Png.incrementNatAt freqs matchSym)[matchSym]! :=
    incrementNatAt_get!_pos freqs matchSym hidx
  have hrec :=
    litLenSymbolFreqsAux_pos_of_pos tokens (i + 1)
      (Png.incrementNatAt freqs matchSym) matchSym hinc
  simpa [h, ht, matchSym] using hrec

/-- If a literal appears at or after the current scan position, the completed
scan gives that literal symbol a positive frequency. -/
lemma litLenSymbolFreqsAux_literal_pos_at
    (tokens : Array Png.DeflateToken) (i target : Nat)
    (freqs : Array Nat) (b : UInt8)
    (hle : i ≤ target)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b)
    (hidx : b.toNat < freqs.size) :
    0 < (Png.litLenSymbolFreqsAux tokens i freqs)[b.toNat]! := by
  by_cases heq : i = target
  · subst target
    exact litLenSymbolFreqsAux_literal_pos_of_current tokens i freqs b htarget ht hidx
  · have hltTarget : i < target := Nat.lt_of_le_of_ne hle heq
    rw [Png.litLenSymbolFreqsAux.eq_1]
    have hi : i < tokens.size := Nat.lt_trans hltTarget htarget
    cases htcur : tokens[i]'hi with
    | literal b0 =>
        have hidx' : b.toNat < (Png.incrementNatAt freqs b0.toNat).size := by
          simpa using hidx
        have hrec :=
          litLenSymbolFreqsAux_literal_pos_at tokens (i + 1) target
            (Png.incrementNatAt freqs b0.toNat) b
            (Nat.succ_le_of_lt hltTarget) htarget ht hidx'
        simpa [hi, htcur] using hrec
    | matchDist1 len =>
        let matchSym := (Png.fixedLenMatchInfo len).1
        have hidx' : b.toNat < (Png.incrementNatAt freqs matchSym).size := by
          simpa using hidx
        have hrec :=
          litLenSymbolFreqsAux_literal_pos_at tokens (i + 1) target
            (Png.incrementNatAt freqs matchSym) b
            (Nat.succ_le_of_lt hltTarget) htarget ht hidx'
        simpa [hi, htcur, matchSym] using hrec
termination_by target - i
decreasing_by
  all_goals
    have hlt : i < target := hltTarget
    exact Nat.sub_lt_sub_left (k := i) (m := target) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- If a match appears at or after the current scan position, the completed
scan gives that match's literal/length symbol a positive frequency. -/
lemma litLenSymbolFreqsAux_match_pos_at
    (tokens : Array Png.DeflateToken) (i target : Nat)
    (freqs : Array Nat) (len : Nat)
    (hle : i ≤ target)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hidx : (Png.fixedLenMatchInfo len).1 < freqs.size) :
    0 <
      (Png.litLenSymbolFreqsAux tokens i freqs)[(Png.fixedLenMatchInfo len).1]! := by
  by_cases heq : i = target
  · subst target
    exact litLenSymbolFreqsAux_match_pos_of_current tokens i freqs len htarget ht hidx
  · have hltTarget : i < target := Nat.lt_of_le_of_ne hle heq
    rw [Png.litLenSymbolFreqsAux.eq_1]
    have hi : i < tokens.size := Nat.lt_trans hltTarget htarget
    cases htcur : tokens[i]'hi with
    | literal b0 =>
        have hidx' :
            (Png.fixedLenMatchInfo len).1 <
              (Png.incrementNatAt freqs b0.toNat).size := by
          simpa using hidx
        have hrec :=
          litLenSymbolFreqsAux_match_pos_at tokens (i + 1) target
            (Png.incrementNatAt freqs b0.toNat) len
            (Nat.succ_le_of_lt hltTarget) htarget ht hidx'
        simpa [hi, htcur] using hrec
    | matchDist1 currentLen =>
        let matchSym := (Png.fixedLenMatchInfo currentLen).1
        have hidx' :
            (Png.fixedLenMatchInfo len).1 <
              (Png.incrementNatAt freqs matchSym).size := by
          simpa using hidx
        have hrec :=
          litLenSymbolFreqsAux_match_pos_at tokens (i + 1) target
            (Png.incrementNatAt freqs matchSym) len
            (Nat.succ_le_of_lt hltTarget) htarget ht hidx'
        simpa [hi, htcur, matchSym] using hrec
termination_by target - i
decreasing_by
  all_goals
    have hlt : i < target := hltTarget
    exact Nat.sub_lt_sub_left (k := i) (m := target) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- A literal token contributes a positive final literal/length frequency for
its byte symbol after the EOB increment is also applied. -/
lemma litLenSymbolFreqs_literal_pos_at
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b) :
    0 < (Png.litLenSymbolFreqs tokens)[b.toNat]! := by
  unfold Png.litLenSymbolFreqs
  have hidx : b.toNat < (Array.replicate 286 0).size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    simpa using (by omega : b.toNat < 286)
  have hpos :
      0 <
        (Png.litLenSymbolFreqsAux tokens 0
          (Array.replicate 286 0))[b.toNat]! :=
    litLenSymbolFreqsAux_literal_pos_at tokens 0 target
      (Array.replicate 286 0) b (Nat.zero_le target) htarget ht hidx
  exact incrementNatAt_get!_pos_of_pos
    (Png.litLenSymbolFreqsAux tokens 0 (Array.replicate 286 0)) 256
    b.toNat hpos

/-- Valid DEFLATE match lengths map to literal/length symbols inside the
generated literal/length table. -/
lemma fixedLenMatchInfo_sym_lt_286
    (len : Nat) (hlen : 3 ≤ len ∧ len ≤ 258) :
    (Png.fixedLenMatchInfo len).1 < 286 := by
  have hinfo := Png.fixedLenMatchInfo_spec_get! len hlen.1 hlen.2
  rcases hfixed : Png.fixedLenMatchInfo len with ⟨sym, extraBits, extraLen⟩
  have hspec :
      257 ≤ sym ∧ sym ≤ 285 ∧
        extraLen = Png.lengthExtra[sym - 257]! ∧
        Png.lengthBases[sym - 257]! + extraBits = len ∧
        extraBits < 2 ^ extraLen := by
    simpa [hfixed] using hinfo
  simpa [hfixed] using (by omega : sym < 286)

/-- A valid match token contributes a positive final literal/length frequency
for its match-length symbol after the EOB increment is also applied. -/
lemma litLenSymbolFreqs_match_pos_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    0 < (Png.litLenSymbolFreqs tokens)[(Png.fixedLenMatchInfo len).1]! := by
  unfold Png.litLenSymbolFreqs
  have hidx : (Png.fixedLenMatchInfo len).1 < (Array.replicate 286 0).size := by
    simpa using fixedLenMatchInfo_sym_lt_286 len hlen
  have hpos :
      0 <
        (Png.litLenSymbolFreqsAux tokens 0
          (Array.replicate 286 0))[(Png.fixedLenMatchInfo len).1]! :=
    litLenSymbolFreqsAux_match_pos_at tokens 0 target
      (Array.replicate 286 0) len (Nat.zero_le target) htarget ht hidx
  exact incrementNatAt_get!_pos_of_pos
    (Png.litLenSymbolFreqsAux tokens 0 (Array.replicate 286 0)) 256
    (Png.fixedLenMatchInfo len).1 hpos

/-- Literal/length frequency collection always assigns a positive count to EOB.
The generated dynamic encoder must be able to terminate every block. -/
lemma litLenSymbolFreqs_eob_pos (tokens : Array Png.DeflateToken) :
    0 < (Png.litLenSymbolFreqs tokens)[256]! := by
  unfold Png.litLenSymbolFreqs
  have hsize :
      (Png.litLenSymbolFreqsAux tokens 0 (Array.replicate 286 0)).size = 286 := by
    simpa using
      (litLenSymbolFreqsAux_size tokens 0 (Array.replicate 286 0))
  have hidx :
      256 < (Png.litLenSymbolFreqsAux tokens 0 (Array.replicate 286 0)).size := by
    omega
  exact incrementNatAt_get!_pos
    (Png.litLenSymbolFreqsAux tokens 0 (Array.replicate 286 0)) 256 hidx

/-- Distance frequency accumulation preserves whatever table shape it is given.
The final table-size theorem instantiates this with the DEFLATE distance size. -/
lemma distSymbolFreqsAux_size
    (tokens : Array Png.DeflateToken) (i : Nat) (freqs : Array Nat) :
    (Png.distSymbolFreqsAux tokens i freqs).size = freqs.size := by
  rw [Png.distSymbolFreqsAux.eq_1]
  by_cases h : i < tokens.size
  · cases ht : tokens[i]'h with
    | literal b =>
        have hrec := distSymbolFreqsAux_size tokens (i + 1) freqs
        simp [h, ht, hrec]
    | matchDist1 len =>
        have hrec := distSymbolFreqsAux_size tokens (i + 1) (Png.incrementNatAt freqs 0)
        simp [h, ht, hrec]
  · simp [h]
termination_by tokens.size - i
decreasing_by
  all_goals
    have hlt : i < tokens.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1) hlt (Nat.lt_succ_self i)

/-- Distance frequency collection keeps the DEFLATE distance table size. This is
needed before proving generated `HDIST` and distance-1 payload lookup. -/
lemma distSymbolFreqs_size (tokens : Array Png.DeflateToken) :
    (Png.distSymbolFreqs tokens).size = 30 := by
  simp [Png.distSymbolFreqs, distSymbolFreqsAux_size]

/-- Once the distance-0 frequency is positive, the remaining frequency scan
preserves that availability fact. -/
lemma distSymbolFreqsAux_zero_pos_of_pos
    (tokens : Array Png.DeflateToken) (i : Nat) (freqs : Array Nat)
    (hpos : 0 < freqs[0]!) :
    0 < (Png.distSymbolFreqsAux tokens i freqs)[0]! := by
  rw [Png.distSymbolFreqsAux.eq_1]
  by_cases h : i < tokens.size
  · cases ht : tokens[i]'h with
    | literal b =>
        have hrec := distSymbolFreqsAux_zero_pos_of_pos tokens (i + 1) freqs hpos
        simpa [h, ht] using hrec
    | matchDist1 len =>
        have hsize : 0 < freqs.size := get!_zero_pos_implies_size_pos freqs hpos
        have hinc : 0 < (Png.incrementNatAt freqs 0)[0]! :=
          incrementNatAt_get!_pos freqs 0 hsize
        have hrec :=
          distSymbolFreqsAux_zero_pos_of_pos tokens (i + 1)
            (Png.incrementNatAt freqs 0) hinc
        simpa [h, ht] using hrec
  · simp [h, hpos]
termination_by tokens.size - i
decreasing_by
  all_goals
    have hlt : i < tokens.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- If the token scanner finds a distance-1 match, distance symbol `0` receives
a positive frequency by the end of distance frequency collection. -/
lemma distSymbolFreqsAux_zero_pos_of_hasMatch
    (tokens : Array Png.DeflateToken) (i : Nat) (freqs : Array Nat)
    (hsize : 0 < freqs.size)
    (hmatch : Png.deflateTokensHasMatchDist1Aux tokens i = true) :
    0 < (Png.distSymbolFreqsAux tokens i freqs)[0]! := by
  rw [Png.deflateTokensHasMatchDist1Aux.eq_1] at hmatch
  rw [Png.distSymbolFreqsAux.eq_1]
  by_cases h : i < tokens.size
  · cases ht : tokens[i]'h with
    | literal b =>
        have hnext : Png.deflateTokensHasMatchDist1Aux tokens (i + 1) = true := by
          simpa [h, ht] using hmatch
        have hrec :=
          distSymbolFreqsAux_zero_pos_of_hasMatch tokens (i + 1) freqs hsize hnext
        simpa [h, ht] using hrec
    | matchDist1 len =>
        have hinc : 0 < (Png.incrementNatAt freqs 0)[0]! :=
          incrementNatAt_get!_pos freqs 0 hsize
        have hrec :=
          distSymbolFreqsAux_zero_pos_of_pos tokens (i + 1)
            (Png.incrementNatAt freqs 0) hinc
        simpa [h, ht] using hrec
  · simp [h] at hmatch
termination_by tokens.size - i
decreasing_by
  all_goals
    have hlt : i < tokens.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- A token stream containing a distance-1 match gives generated distance
symbol `0` a positive frequency. -/
lemma distSymbolFreqs_zero_pos_of_hasMatch
    (tokens : Array Png.DeflateToken)
    (hmatch : Png.deflateTokensHasMatchDist1 tokens = true) :
    0 < (Png.distSymbolFreqs tokens)[0]! := by
  unfold Png.deflateTokensHasMatchDist1 at hmatch
  unfold Png.distSymbolFreqs
  exact distSymbolFreqsAux_zero_pos_of_hasMatch tokens 0
    (Array.replicate 30 0) (by decide) hmatch

/-- A match token at or after the current scanner position makes the match
detector return true. This connects indexed payload tokens to distance tables. -/
lemma deflateTokensHasMatchDist1Aux_true_of_match_at
    (tokens : Array Png.DeflateToken) (i target len : Nat)
    (hle : i ≤ target)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len) :
    Png.deflateTokensHasMatchDist1Aux tokens i = true := by
  by_cases heq : i = target
  · subst target
    rw [Png.deflateTokensHasMatchDist1Aux.eq_1]
    simp [htarget, ht]
  · have hltTarget : i < target := Nat.lt_of_le_of_ne hle heq
    rw [Png.deflateTokensHasMatchDist1Aux.eq_1]
    have hi : i < tokens.size := Nat.lt_trans hltTarget htarget
    cases htcur : tokens[i]'hi with
    | literal b =>
        have hrec :=
          deflateTokensHasMatchDist1Aux_true_of_match_at tokens (i + 1)
            target len (Nat.succ_le_of_lt hltTarget) htarget ht
        simpa [hi, htcur] using hrec
    | matchDist1 currentLen =>
        simp [hi, htcur]
termination_by target - i
decreasing_by
  all_goals
    have hlt : i < target := hltTarget
    exact Nat.sub_lt_sub_left (k := i) (m := target) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- A match token anywhere in the token stream makes the top-level match
detector return true. -/
lemma deflateTokensHasMatchDist1_true_of_match_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len) :
    Png.deflateTokensHasMatchDist1 tokens = true := by
  unfold Png.deflateTokensHasMatchDist1
  exact deflateTokensHasMatchDist1Aux_true_of_match_at tokens 0 target len
    (Nat.zero_le target) htarget ht

/-- The generated literal/length code length is positive. This is the nonzero
branch used for every symbol selected by the frequency table. -/
lemma generatedDynamicLitLenCodeLen_pos :
    0 < Png.generatedDynamicLitLenCodeLen := by
  simp [Png.generatedDynamicLitLenCodeLen]

/-- The generated literal/length code length fits in DEFLATE's 15-bit limit.
This is the value bound used by generated table validity proofs. -/
lemma generatedDynamicLitLenCodeLen_le_15 :
    Png.generatedDynamicLitLenCodeLen ≤ 15 := by
  simp [Png.generatedDynamicLitLenCodeLen]

/-- The generated literal/length code length is concretely 9 bits. This
packages the encoder choice for finite code-space proofs. -/
lemma generatedDynamicLitLenCodeLen_eq_nine :
    Png.generatedDynamicLitLenCodeLen = 9 := rfl

/-- A generated literal/length code-length entry is always a valid DEFLATE code
length. This follows directly from the by-index generator. -/
lemma generatedDynamicLitLenLengthAt_le_15 (freqs : Array Nat) (idx : Nat) :
    Png.generatedDynamicLitLenLengthAt freqs idx ≤ 15 := by
  unfold Png.generatedDynamicLitLenLengthAt
  by_cases h : freqs[idx]! > 0
  · simp [h, generatedDynamicLitLenCodeLen_le_15]
  · simp [h]

/-- A generated literal/length entry never exceeds the encoder's uniform
literal/length code size. This is the sharp bound for canonical-table proofs. -/
lemma generatedDynamicLitLenLengthAt_le_codeLen
    (freqs : Array Nat) (idx : Nat) :
    Png.generatedDynamicLitLenLengthAt freqs idx ≤
      Png.generatedDynamicLitLenCodeLen := by
  unfold Png.generatedDynamicLitLenLengthAt
  by_cases h : freqs[idx]! > 0
  · simp [h]
  · simp [h]

/-- A generated literal/length code-length entry is either zero or the uniform
generated length. This is the entry-level shape used by table proofs. -/
lemma generatedDynamicLitLenLengthAt_eq_zero_or_codeLen
    (freqs : Array Nat) (idx : Nat) :
    Png.generatedDynamicLitLenLengthAt freqs idx = 0 ∨
      Png.generatedDynamicLitLenLengthAt freqs idx =
        Png.generatedDynamicLitLenCodeLen := by
  unfold Png.generatedDynamicLitLenLengthAt
  by_cases hfreq : freqs[idx]! > 0
  · simp [hfreq]
  · simp [hfreq]

/-- A positive literal/length frequency produces a positive generated code
length. This bridges frequency availability to generated table availability. -/
lemma generatedDynamicLitLenLengthAt_pos_of_freq
    (freqs : Array Nat) (idx : Nat)
    (hfreq : 0 < freqs[idx]!) :
    0 < Png.generatedDynamicLitLenLengthAt freqs idx := by
  unfold Png.generatedDynamicLitLenLengthAt
  simp [hfreq, generatedDynamicLitLenCodeLen_pos]

/-- Generated literal/length entries are positive exactly for symbols with a
positive collected frequency. This is the local availability iff. -/
lemma generatedDynamicLitLenLengthAt_pos_iff
    (freqs : Array Nat) (idx : Nat) :
    0 < Png.generatedDynamicLitLenLengthAt freqs idx ↔
      0 < freqs[idx]! := by
  unfold Png.generatedDynamicLitLenLengthAt
  by_cases hfreq : 0 < freqs[idx]!
  · simp [hfreq, generatedDynamicLitLenCodeLen_pos]
  · simp [hfreq]

/-- Generated literal/length code lengths preserve the input frequency table
size, so later header proofs can reason about table bounds. -/
lemma generatedDynamicLitLenLengths_size (freqs : Array Nat) :
    (Png.generatedDynamicLitLenLengths freqs).size = freqs.size := by
  simp [Png.generatedDynamicLitLenLengths]

/-- Generated literal/length tables built from generated token streams have the
full DEFLATE literal/length-table size. -/
lemma generatedDynamicLitLenLengths_size_286
    (tokens : Array Png.DeflateToken) :
    (Png.generatedDynamicLitLenLengths
      (Png.litLenSymbolFreqs tokens)).size = 286 := by
  simp [generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]

/-- Every in-bounds generated literal/length code-length entry satisfies
DEFLATE's 15-bit limit. This is the table-level validity shape for `HLIT`. -/
lemma generatedDynamicLitLenLengths_getElem_le_15
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicLitLenLengths freqs).size) :
    (Png.generatedDynamicLitLenLengths freqs)[idx] ≤ 15 := by
  simpa [Png.generatedDynamicLitLenLengths] using
    generatedDynamicLitLenLengthAt_le_15 freqs idx

/-- Every in-bounds generated literal/length entry is bounded by the uniform
code length. This table-level form feeds the max-code-length scan proof. -/
lemma generatedDynamicLitLenLengths_getElem_le_codeLen
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicLitLenLengths freqs).size) :
    (Png.generatedDynamicLitLenLengths freqs)[idx] ≤
      Png.generatedDynamicLitLenCodeLen := by
  simpa [Png.generatedDynamicLitLenLengths] using
    generatedDynamicLitLenLengthAt_le_codeLen freqs idx

/-- In-bounds generated literal/length table entries use only the generator's
zero-or-uniform shape. This lifts the entry shape to array indexing. -/
lemma generatedDynamicLitLenLengths_getElem_eq_zero_or_codeLen
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicLitLenLengths freqs).size) :
    (Png.generatedDynamicLitLenLengths freqs)[idx] = 0 ∨
      (Png.generatedDynamicLitLenLengths freqs)[idx] =
        Png.generatedDynamicLitLenCodeLen := by
  simpa [Png.generatedDynamicLitLenLengths] using
    generatedDynamicLitLenLengthAt_eq_zero_or_codeLen freqs idx

/-- In-bounds generated literal/length table entries are concretely either
unused or 9-bit codes. This is the finite alphabet shape used by table proofs. -/
lemma generatedDynamicLitLenLengths_getElem_eq_zero_or_nine
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicLitLenLengths freqs).size) :
    (Png.generatedDynamicLitLenLengths freqs)[idx] = 0 ∨
      (Png.generatedDynamicLitLenLengths freqs)[idx] = 9 := by
  rcases generatedDynamicLitLenLengths_getElem_eq_zero_or_codeLen freqs idx hidx
    with hzero | hcode
  · exact Or.inl hzero
  · exact Or.inr (by simpa [generatedDynamicLitLenCodeLen_eq_nine] using hcode)

/-- For generated literal/length entries, positivity is equivalent to being a
9-bit entry. This turns availability facts into concrete code-length facts. -/
lemma generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicLitLenLengths freqs).size) :
    0 < (Png.generatedDynamicLitLenLengths freqs)[idx] ↔
      (Png.generatedDynamicLitLenLengths freqs)[idx] = 9 := by
  constructor
  · intro hpos
    rcases generatedDynamicLitLenLengths_getElem_eq_zero_or_nine freqs idx hidx
      with hzero | hnine
    · omega
    · exact hnine
  · intro hnine
    omega

/-- In `get!` form, a generated literal/length table entry is positive exactly
when its source frequency is positive. This matches payload lookup code. -/
lemma generatedDynamicLitLenLengths_get!_pos_iff
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < freqs.size) :
    0 < (Png.generatedDynamicLitLenLengths freqs)[idx]! ↔
      0 < freqs[idx]! := by
  have hidxLengths : idx < (Png.generatedDynamicLitLenLengths freqs).size := by
    simpa [generatedDynamicLitLenLengths_size] using hidx
  rw [getElem!_pos (Png.generatedDynamicLitLenLengths freqs) idx hidxLengths]
  simpa [Png.generatedDynamicLitLenLengths] using
    generatedDynamicLitLenLengthAt_pos_iff freqs idx

/-- In `get!` form, generated literal/length entries still use only the
zero-or-uniform shape. This matches helper code that indexes with `get!`. -/
lemma generatedDynamicLitLenLengths_get!_eq_zero_or_codeLen
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicLitLenLengths freqs).size) :
    (Png.generatedDynamicLitLenLengths freqs)[idx]! = 0 ∨
      (Png.generatedDynamicLitLenLengths freqs)[idx]! =
        Png.generatedDynamicLitLenCodeLen := by
  rw [getElem!_pos (Png.generatedDynamicLitLenLengths freqs) idx hidx]
  exact generatedDynamicLitLenLengths_getElem_eq_zero_or_codeLen
    freqs idx hidx

/-- In `get!` form, generated literal/length entries are concretely either
unused or 9-bit codes. This matches the writer's lookup style. -/
lemma generatedDynamicLitLenLengths_get!_eq_zero_or_nine
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicLitLenLengths freqs).size) :
    (Png.generatedDynamicLitLenLengths freqs)[idx]! = 0 ∨
      (Png.generatedDynamicLitLenLengths freqs)[idx]! = 9 := by
  rw [getElem!_pos (Png.generatedDynamicLitLenLengths freqs) idx hidx]
  exact generatedDynamicLitLenLengths_getElem_eq_zero_or_nine freqs idx hidx

/-- In `get!` form, generated literal/length positivity is equivalent to the
concrete 9-bit code length. This matches payload-code lookup proofs. -/
lemma generatedDynamicLitLenLengths_get!_pos_iff_eq_nine
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicLitLenLengths freqs).size) :
    0 < (Png.generatedDynamicLitLenLengths freqs)[idx]! ↔
      (Png.generatedDynamicLitLenLengths freqs)[idx]! = 9 := by
  rw [getElem!_pos (Png.generatedDynamicLitLenLengths freqs) idx hidx]
  exact generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine freqs idx hidx

/-- The generated literal/length length table always contains EOB in bounds.
This packages the fixed table-size facts for later payload proofs. -/
lemma generatedDynamicLitLenLengths_eob_inBounds
    (tokens : Array Png.DeflateToken) :
    256 <
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqs tokens)).size := by
  simp [generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]

/-- Generated literal/length lengths always contain a positive EOB entry. This
is the table availability fact needed before proving generated block payloads. -/
lemma generatedDynamicLitLenLengths_eob_pos (tokens : Array Png.DeflateToken) :
    0 <
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqs tokens))[256]'
          (generatedDynamicLitLenLengths_eob_inBounds tokens) := by
  let freqs := Png.litLenSymbolFreqs tokens
  have hfreq : 0 < freqs[256]! := by
    simpa [freqs] using litLenSymbolFreqs_eob_pos tokens
  have hpos : 0 < Png.generatedDynamicLitLenLengthAt freqs 256 :=
    generatedDynamicLitLenLengthAt_pos_of_freq freqs 256 hfreq
  simpa [Png.generatedDynamicLitLenLengths, freqs] using hpos

/-- Generated literal/length tables assign EOB the concrete 9-bit code length.
This is the termination-symbol shape needed by generated payload proofs. -/
lemma generatedDynamicLitLenLengths_eob_eq_nine
    (tokens : Array Png.DeflateToken) :
    (Png.generatedDynamicLitLenLengths
      (Png.litLenSymbolFreqs tokens))[256]'
        (generatedDynamicLitLenLengths_eob_inBounds tokens) = 9 := by
  have hpos := generatedDynamicLitLenLengths_eob_pos tokens
  exact
    (generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine
      (Png.litLenSymbolFreqs tokens) 256
      (generatedDynamicLitLenLengths_eob_inBounds tokens)).mp hpos

/-- Literal tokens receive positive generated literal/length code lengths. This
connects token frequency collection to later payload-code lookup. -/
lemma generatedDynamicLitLenLengths_literal_pos_at
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b) :
    0 <
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqs tokens))[b.toNat]! := by
  let freqs := Png.litLenSymbolFreqs tokens
  have hfreq : 0 < freqs[b.toNat]! := by
    simpa [freqs] using litLenSymbolFreqs_literal_pos_at tokens target b htarget ht
  have hpos :
      0 < Png.generatedDynamicLitLenLengthAt freqs b.toNat :=
    generatedDynamicLitLenLengthAt_pos_of_freq freqs b.toNat hfreq
  have hidx :
      b.toNat < (Png.generatedDynamicLitLenLengths freqs).size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    have hsize :
        (Png.generatedDynamicLitLenLengths freqs).size = 286 := by
      simp [generatedDynamicLitLenLengths_size, freqs, litLenSymbolFreqs_size]
    omega
  change 0 < (Png.generatedDynamicLitLenLengths freqs)[b.toNat]!
  rw [getElem!_pos (Png.generatedDynamicLitLenLengths freqs) b.toNat hidx]
  simpa [Png.generatedDynamicLitLenLengths, freqs] using hpos

/-- Literal tokens receive concrete 9-bit generated literal/length entries.
This strengthens payload-code availability from positivity to exact length. -/
lemma generatedDynamicLitLenLengths_literal_eq_nine_at
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b) :
    (Png.generatedDynamicLitLenLengths
      (Png.litLenSymbolFreqs tokens))[b.toNat]! = 9 := by
  let freqs := Png.litLenSymbolFreqs tokens
  have hidx :
      b.toNat < (Png.generatedDynamicLitLenLengths freqs).size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    have hsize :
        (Png.generatedDynamicLitLenLengths freqs).size = 286 := by
      simp [generatedDynamicLitLenLengths_size, freqs, litLenSymbolFreqs_size]
    omega
  have hpos :
      0 < (Png.generatedDynamicLitLenLengths freqs)[b.toNat]! := by
    simpa [freqs] using
      generatedDynamicLitLenLengths_literal_pos_at tokens target b htarget ht
  exact
    (generatedDynamicLitLenLengths_get!_pos_iff_eq_nine freqs b.toNat hidx).mp hpos

/-- Valid match tokens receive positive generated literal/length code lengths.
This is the match-symbol counterpart of literal payload availability. -/
lemma generatedDynamicLitLenLengths_match_pos_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    0 <
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqs tokens))[(Png.fixedLenMatchInfo len).1]! := by
  let freqs := Png.litLenSymbolFreqs tokens
  have hfreq : 0 < freqs[(Png.fixedLenMatchInfo len).1]! := by
    simpa [freqs] using
      litLenSymbolFreqs_match_pos_at tokens target len htarget ht hlen
  have hpos :
      0 < Png.generatedDynamicLitLenLengthAt freqs (Png.fixedLenMatchInfo len).1 :=
    generatedDynamicLitLenLengthAt_pos_of_freq freqs (Png.fixedLenMatchInfo len).1 hfreq
  have hidx :
      (Png.fixedLenMatchInfo len).1 <
        (Png.generatedDynamicLitLenLengths freqs).size := by
    have hsym := fixedLenMatchInfo_sym_lt_286 len hlen
    have hsize :
        (Png.generatedDynamicLitLenLengths freqs).size = 286 := by
      simp [generatedDynamicLitLenLengths_size, freqs, litLenSymbolFreqs_size]
    omega
  change
    0 <
      (Png.generatedDynamicLitLenLengths freqs)[(Png.fixedLenMatchInfo len).1]!
  rw [getElem!_pos (Png.generatedDynamicLitLenLengths freqs)
    (Png.fixedLenMatchInfo len).1 hidx]
  simpa [Png.generatedDynamicLitLenLengths, freqs] using hpos

/-- Valid match tokens receive concrete 9-bit generated literal/length entries.
This is the exact-length counterpart of match-symbol availability. -/
lemma generatedDynamicLitLenLengths_match_eq_nine_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    (Png.generatedDynamicLitLenLengths
      (Png.litLenSymbolFreqs tokens))[(Png.fixedLenMatchInfo len).1]! = 9 := by
  let freqs := Png.litLenSymbolFreqs tokens
  have hidx :
      (Png.fixedLenMatchInfo len).1 <
        (Png.generatedDynamicLitLenLengths freqs).size := by
    have hsym := fixedLenMatchInfo_sym_lt_286 len hlen
    have hsize :
        (Png.generatedDynamicLitLenLengths freqs).size = 286 := by
      simp [generatedDynamicLitLenLengths_size, freqs, litLenSymbolFreqs_size]
    omega
  have hpos :
      0 <
        (Png.generatedDynamicLitLenLengths freqs)[(Png.fixedLenMatchInfo len).1]! := by
    simpa [freqs] using
      generatedDynamicLitLenLengths_match_pos_at tokens target len htarget ht hlen
  exact
    (generatedDynamicLitLenLengths_get!_pos_iff_eq_nine
      freqs (Png.fixedLenMatchInfo len).1 hidx).mp hpos

/-- Match tokens from the public generated tokenizer receive positive generated
literal/length entries without needing a separate length assumption. -/
lemma generatedDynamicLitLenLengths_match_pos_at_deflateTokensDist1
    (raw : ByteArray) (target len : Nat)
    (htarget : target < (Png.deflateTokensDist1 raw).size)
    (ht : (Png.deflateTokensDist1 raw)[target]'htarget =
      Png.DeflateToken.matchDist1 len) :
    0 <
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqs
          (Png.deflateTokensDist1 raw)))[(Png.fixedLenMatchInfo len).1]! := by
  have hlen := deflateTokensDist1_match_len_bounds_at raw target len htarget ht
  exact generatedDynamicLitLenLengths_match_pos_at
    (Png.deflateTokensDist1 raw) target len htarget ht hlen

/-- Generated distance code lengths preserve the input frequency table size,
including the single-symbol distance-1 case. -/
lemma generatedDynamicDistLengths_size (freqs : Array Nat) :
    (Png.generatedDynamicDistLengths freqs).size = freqs.size := by
  simp [Png.generatedDynamicDistLengths]

/-- A generated distance code-length entry is always valid for DEFLATE. The
current generated encoder only emits the distance-1 alphabet entry. -/
lemma generatedDynamicDistLengthAt_le_15 (freqs : Array Nat) (idx : Nat) :
    Png.generatedDynamicDistLengthAt freqs idx ≤ 15 := by
  unfold Png.generatedDynamicDistLengthAt
  by_cases h : idx == 0 && freqs[0]! > 0 <;> simp [h]

/-- A positive distance-symbol-0 frequency produces a positive generated
distance code length at index zero. -/
lemma generatedDynamicDistLengthAt_zero_pos_of_freq
    (freqs : Array Nat)
    (hfreq : 0 < freqs[0]!) :
    0 < Png.generatedDynamicDistLengthAt freqs 0 := by
  unfold Png.generatedDynamicDistLengthAt
  simp [hfreq]

/-- Generated distance entry zero is positive exactly when distance symbol zero
has a positive collected frequency. -/
lemma generatedDynamicDistLengthAt_zero_pos_iff
    (freqs : Array Nat) :
    0 < Png.generatedDynamicDistLengthAt freqs 0 ↔
      0 < freqs[0]! := by
  unfold Png.generatedDynamicDistLengthAt
  by_cases hfreq : 0 < freqs[0]!
  · simp [hfreq]
  · simp [hfreq]

/-- Every in-bounds generated distance code-length entry satisfies DEFLATE's
15-bit limit. This is the table-level validity shape for `HDIST`. -/
lemma generatedDynamicDistLengths_getElem_le_15
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicDistLengths freqs).size) :
    (Png.generatedDynamicDistLengths freqs)[idx] ≤ 15 := by
  simpa [Png.generatedDynamicDistLengths] using
    generatedDynamicDistLengthAt_le_15 freqs idx

/-- If every remaining array entry is bounded, `maxCodeLenAux` stays bounded.
This isolates the recursive scan needed by generated Huffman-table proofs. -/
lemma maxCodeLenAux_le_of_getElem_le
    (lengths : Array Nat) (i maxLen bound : Nat)
    (hmax : maxLen ≤ bound)
    (hentries : ∀ j (hj : j < lengths.size), i ≤ j -> lengths[j] ≤ bound) :
    Png.maxCodeLenAux lengths i maxLen ≤ bound := by
  rw [Png.maxCodeLenAux.eq_1]
  by_cases hi : i < lengths.size
  · have hlen : lengths[i] ≤ bound := hentries i hi le_rfl
    by_cases hgt : lengths[i] > maxLen
    · have hrec :
          Png.maxCodeLenAux lengths (i + 1) lengths[i] ≤ bound :=
        maxCodeLenAux_le_of_getElem_le lengths (i + 1) lengths[i] bound
          hlen
          (by
            intro j hj hij
            exact hentries j hj (by omega))
      simp [hi, hgt]
      exact hrec
    · have hrec :
          Png.maxCodeLenAux lengths (i + 1) maxLen ≤ bound :=
        maxCodeLenAux_le_of_getElem_le lengths (i + 1) maxLen bound
          hmax
          (by
            intro j hj hij
            exact hentries j hj (by omega))
      simp [hi, hgt]
      exact hrec
  · simp [hi, hmax]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- The generated literal/length table's scanned maximum code length is within
DEFLATE's limit. This prepares the literal/length `mkHuffman` validity proof. -/
lemma maxCodeLenAux_generatedDynamicLitLenLengths_le_15
    (freqs : Array Nat) (i maxLen : Nat)
    (hmax : maxLen ≤ 15) :
    Png.maxCodeLenAux (Png.generatedDynamicLitLenLengths freqs) i maxLen ≤ 15 := by
  exact maxCodeLenAux_le_of_getElem_le
    (Png.generatedDynamicLitLenLengths freqs) i maxLen 15 hmax
    (by
      intro j hj _hij
      exact generatedDynamicLitLenLengths_getElem_le_15 freqs j hj)

/-- The generated literal/length table's scanned maximum is bounded by the
uniform literal/length code size. This is the sharp generated-table max bound. -/
lemma maxCodeLenAux_generatedDynamicLitLenLengths_le_codeLen
    (freqs : Array Nat) (i maxLen : Nat)
    (hmax : maxLen ≤ Png.generatedDynamicLitLenCodeLen) :
    Png.maxCodeLenAux (Png.generatedDynamicLitLenLengths freqs) i maxLen ≤
      Png.generatedDynamicLitLenCodeLen := by
  exact maxCodeLenAux_le_of_getElem_le
    (Png.generatedDynamicLitLenLengths freqs) i maxLen
    Png.generatedDynamicLitLenCodeLen hmax
    (by
      intro j hj _hij
      exact generatedDynamicLitLenLengths_getElem_le_codeLen freqs j hj)

/-- Generated literal/length tables have enough 9-bit code space for every
possible literal/length symbol. This is the finite alphabet-size side of
canonical-table validity. -/
lemma generatedDynamicLitLenLengths_size_le_codeSpace
    (tokens : Array Png.DeflateToken) :
    (Png.generatedDynamicLitLenLengths
      (Png.litLenSymbolFreqs tokens)).size ≤
        2 ^ Png.generatedDynamicLitLenCodeLen := by
  simp [generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size,
    Png.generatedDynamicLitLenCodeLen]

/-- The generated literal/length code space is concretely 512 codes. This is
the numeric side of the 9-bit generated table validity argument. -/
lemma generatedDynamicLitLenCodeSpace_eq_512 :
    2 ^ Png.generatedDynamicLitLenCodeLen = 512 := by
  simp [Png.generatedDynamicLitLenCodeLen]

/-- Generated literal/length tables have strictly fewer entries than the
available 9-bit code space. This is stronger than needed for non-oversubscribe. -/
lemma generatedDynamicLitLenLengths_size_lt_codeSpace
    (tokens : Array Png.DeflateToken) :
    (Png.generatedDynamicLitLenLengths
      (Png.litLenSymbolFreqs tokens)).size <
        2 ^ Png.generatedDynamicLitLenCodeLen := by
  simp [generatedDynamicLitLenLengths_size_286, generatedDynamicLitLenCodeSpace_eq_512]

/-- Generated literal/length tables fit in the concrete 512-entry 9-bit code
space. This avoids redoing arithmetic in later canonical-code proofs. -/
lemma generatedDynamicLitLenLengths_size_le_512
    (tokens : Array Png.DeflateToken) :
    (Png.generatedDynamicLitLenLengths
      (Png.litLenSymbolFreqs tokens)).size ≤ 512 := by
  simpa [generatedDynamicLitLenCodeSpace_eq_512] using
    generatedDynamicLitLenLengths_size_le_codeSpace tokens

/-- The generated distance table's scanned maximum code length is within
DEFLATE's limit. This is the distance-table counterpart to the lit/len bound. -/
lemma maxCodeLenAux_generatedDynamicDistLengths_le_15
    (freqs : Array Nat) (i maxLen : Nat)
    (hmax : maxLen ≤ 15) :
    Png.maxCodeLenAux (Png.generatedDynamicDistLengths freqs) i maxLen ≤ 15 := by
  exact maxCodeLenAux_le_of_getElem_le
    (Png.generatedDynamicDistLengths freqs) i maxLen 15 hmax
    (by
      intro j hj _hij
      exact generatedDynamicDistLengths_getElem_le_15 freqs j hj)

/-- A positive incoming maximum remains positive after the max-code-length
scan. This is the base lower-bound helper for generated table validity. -/
lemma maxCodeLenAux_pos_of_maxLen_pos
    (lengths : Array Nat) (i maxLen : Nat)
    (hmax : 0 < maxLen) :
    0 < Png.maxCodeLenAux lengths i maxLen := by
  rw [Png.maxCodeLenAux.eq_1]
  by_cases hi : i < lengths.size
  · by_cases hgt : lengths[i] > maxLen
    · have hlen : 0 < lengths[i] := by omega
      have hrec :=
        maxCodeLenAux_pos_of_maxLen_pos lengths (i + 1) lengths[i] hlen
      simpa [hi, hgt] using hrec
    · have hrec :=
        maxCodeLenAux_pos_of_maxLen_pos lengths (i + 1) maxLen hmax
      simpa [hi, hgt] using hrec
  · simpa [hi] using hmax
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- If the scan range contains a positive entry, `maxCodeLenAux` returns a
positive maximum. This justifies the nonzero `maxLen` branch for `mkHuffman`. -/
lemma maxCodeLenAux_pos_of_getElem_pos
    (lengths : Array Nat) (i maxLen target : Nat)
    (hle : i ≤ target)
    (htarget : target < lengths.size)
    (hpos : 0 < lengths[target]) :
    0 < Png.maxCodeLenAux lengths i maxLen := by
  rw [Png.maxCodeLenAux.eq_1]
  have hi : i < lengths.size := lt_of_le_of_lt hle htarget
  by_cases hgt : lengths[i] > maxLen
  · have hlen : 0 < lengths[i] := by omega
    have hrec :=
      maxCodeLenAux_pos_of_maxLen_pos lengths (i + 1) lengths[i] hlen
    simpa [hi, hgt] using hrec
  · by_cases heq : i = target
    · subst target
      have hmaxPos : 0 < maxLen := by omega
      have hrec :=
        maxCodeLenAux_pos_of_maxLen_pos lengths (i + 1) maxLen hmaxPos
      simpa [hi, hgt] using hrec
    · have hlt : i < target := Nat.lt_of_le_of_ne hle heq
      have hrec :=
        maxCodeLenAux_pos_of_getElem_pos lengths (i + 1) maxLen target
          (by omega) htarget hpos
      simpa [hi, hgt] using hrec
termination_by lengths.size - i
decreasing_by
  all_goals
    have hltLen : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hltLen (Nat.lt_succ_self i)

/-- The incoming maximum is a lower bound for `maxCodeLenAux`. This exposes the
monotonic part of the max scan used by canonical-table proofs. -/
lemma maxLen_le_maxCodeLenAux
    (lengths : Array Nat) (i maxLen : Nat) :
    maxLen ≤ Png.maxCodeLenAux lengths i maxLen := by
  rw [Png.maxCodeLenAux.eq_1]
  by_cases hi : i < lengths.size
  · by_cases hgt : lengths[i] > maxLen
    · have hrec := maxLen_le_maxCodeLenAux lengths (i + 1) lengths[i]
      have hle : maxLen ≤ lengths[i] := by omega
      simp [hi, hgt]
      exact le_trans hle hrec
    · have hrec := maxLen_le_maxCodeLenAux lengths (i + 1) maxLen
      simpa [hi, hgt] using hrec
  · simp [hi]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Any entry in the scanned suffix is bounded by the final `maxCodeLenAux`
result. This is the lower-bound counterpart to the generated max upper bound. -/
lemma getElem_le_maxCodeLenAux
    (lengths : Array Nat) (i maxLen target : Nat)
    (hle : i ≤ target)
    (htarget : target < lengths.size) :
    lengths[target] ≤ Png.maxCodeLenAux lengths i maxLen := by
  rw [Png.maxCodeLenAux.eq_1]
  have hi : i < lengths.size := lt_of_le_of_lt hle htarget
  by_cases hgt : lengths[i] > maxLen
  · by_cases heq : i = target
    · subst target
      have hrec := maxLen_le_maxCodeLenAux lengths (i + 1) lengths[i]
      simpa [hi, hgt] using hrec
    · have hrec :=
        getElem_le_maxCodeLenAux lengths (i + 1) lengths[i] target
          (by omega) htarget
      simpa [hi, hgt] using hrec
  · by_cases heq : i = target
    · subst target
      have hleCur : lengths[i] ≤ maxLen := by omega
      have hrec := maxLen_le_maxCodeLenAux lengths (i + 1) maxLen
      have hleResult : lengths[i] ≤ Png.maxCodeLenAux lengths (i + 1) maxLen :=
        le_trans hleCur hrec
      simpa [hi, hgt] using hleResult
    · have hrec :=
        getElem_le_maxCodeLenAux lengths (i + 1) maxLen target
          (by omega) htarget
      simpa [hi, hgt] using hrec
termination_by lengths.size - i
decreasing_by
  all_goals
    have hltLen : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hltLen (Nat.lt_succ_self i)

/-- Generated literal/length tables have a positive scanned maximum because
EOB is always assigned a positive generated code length. -/
lemma maxCodeLenAux_generatedDynamicLitLenLengths_pos
    (tokens : Array Png.DeflateToken) :
    0 <
      Png.maxCodeLenAux
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)) 0 0 := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hidx : 256 < lengths.size := by
    simpa [lengths] using generatedDynamicLitLenLengths_eob_inBounds tokens
  have hpos : 0 < lengths[256] := by
    simpa [lengths] using generatedDynamicLitLenLengths_eob_pos tokens
  simpa [lengths] using
    maxCodeLenAux_pos_of_getElem_pos lengths 0 0 256 (by decide) hidx hpos

/-- Generated literal/length tables scan to exactly the uniform 9-bit code
length because EOB is present and no entry can exceed that length. -/
lemma maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen
    (tokens : Array Png.DeflateToken) :
    Png.maxCodeLenAux
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)) 0 0 =
      Png.generatedDynamicLitLenCodeLen := by
  let freqs := Png.litLenSymbolFreqs tokens
  let lengths := Png.generatedDynamicLitLenLengths freqs
  have hidx : 256 < lengths.size := by
    simpa [lengths, freqs] using generatedDynamicLitLenLengths_eob_inBounds tokens
  have hfreq : 0 < freqs[256]! := by
    simpa [freqs] using litLenSymbolFreqs_eob_pos tokens
  have hentry : lengths[256] = Png.generatedDynamicLitLenCodeLen := by
    have hAt :
        Png.generatedDynamicLitLenLengthAt freqs 256 =
          Png.generatedDynamicLitLenCodeLen := by
      unfold Png.generatedDynamicLitLenLengthAt
      simp [hfreq]
    simpa [lengths, Png.generatedDynamicLitLenLengths] using hAt
  have hle :
      Png.maxCodeLenAux lengths 0 0 ≤ Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_le_codeLen freqs 0 0
        (by simp [Png.generatedDynamicLitLenCodeLen])
  have hge :
      Png.generatedDynamicLitLenCodeLen ≤ Png.maxCodeLenAux lengths 0 0 := by
    simpa [hentry] using getElem_le_maxCodeLenAux lengths 0 0 256 (by decide) hidx
  exact le_antisymm hle hge

/-- In `get!` form, generated distance entry zero is positive exactly when the
source distance-symbol-zero frequency is positive. -/
lemma generatedDynamicDistLengths_zero_get!_pos_iff
    (freqs : Array Nat)
    (hsize : 0 < freqs.size) :
    0 < (Png.generatedDynamicDistLengths freqs)[0]! ↔
      0 < freqs[0]! := by
  have hidxLengths : 0 < (Png.generatedDynamicDistLengths freqs).size := by
    simpa [generatedDynamicDistLengths_size] using hsize
  rw [getElem!_pos (Png.generatedDynamicDistLengths freqs) 0 hidxLengths]
  simpa [Png.generatedDynamicDistLengths] using
    generatedDynamicDistLengthAt_zero_pos_iff freqs

/-- The generated distance length table keeps distance symbol `0` in bounds.
The table has the fixed DEFLATE distance-table shape. -/
lemma generatedDynamicDistLengths_zero_inBounds
    (tokens : Array Png.DeflateToken) :
    0 <
      (Png.generatedDynamicDistLengths
        (Png.distSymbolFreqs tokens)).size := by
  simp [generatedDynamicDistLengths_size, distSymbolFreqs_size]

/-- If generated tokens contain a distance-1 match, their generated distance
length table contains a positive length for distance symbol `0`. -/
lemma generatedDynamicDistLengths_zero_pos_of_hasMatch
    (tokens : Array Png.DeflateToken)
    (hmatch : Png.deflateTokensHasMatchDist1 tokens = true) :
    0 <
      (Png.generatedDynamicDistLengths
        (Png.distSymbolFreqs tokens))[0]'
          (generatedDynamicDistLengths_zero_inBounds tokens) := by
  let freqs := Png.distSymbolFreqs tokens
  have hfreq : 0 < freqs[0]! := by
    simpa [freqs] using distSymbolFreqs_zero_pos_of_hasMatch tokens hmatch
  have hpos : 0 < Png.generatedDynamicDistLengthAt freqs 0 :=
    generatedDynamicDistLengthAt_zero_pos_of_freq freqs hfreq
  simpa [Png.generatedDynamicDistLengths, freqs] using hpos

/-- A match token anywhere in the token stream gives distance symbol `0` a
positive generated code length. -/
lemma generatedDynamicDistLengths_zero_pos_of_match_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len) :
    0 <
      (Png.generatedDynamicDistLengths
        (Png.distSymbolFreqs tokens))[0]'
          (generatedDynamicDistLengths_zero_inBounds tokens) := by
  exact generatedDynamicDistLengths_zero_pos_of_hasMatch tokens
    (deflateTokensHasMatchDist1_true_of_match_at tokens target len htarget ht)

/-- Match tokens make the generated distance code length at symbol `0` positive
in the `get!` form used by payload code-table lookup. -/
lemma generatedDynamicDistLengths_zero_get!_pos_of_match_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len) :
    0 <
      (Png.generatedDynamicDistLengths
        (Png.distSymbolFreqs tokens))[0]! := by
  let lengths := Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
  have hidx : 0 < lengths.size := by
    simpa [lengths] using generatedDynamicDistLengths_zero_inBounds tokens
  have hpos : 0 < lengths[0]'hidx := by
    simpa [lengths] using
      generatedDynamicDistLengths_zero_pos_of_match_at tokens target len htarget ht
  change 0 < lengths[0]!
  rw [getElem!_pos lengths 0 hidx]
  exact hpos

/-- With a positive distance-1 frequency, generated distance lengths have the
single-symbol shape accepted by DEFLATE distance tables. -/
lemma generatedDynamicDistLengths_eq_matchShape
    (freqs : Array Nat)
    (hsize : freqs.size = 30)
    (hfreq : 0 < freqs[0]!) :
    Png.generatedDynamicDistLengths freqs =
      Array.ofFn (fun idx : Fin 30 => if idx.val == 0 then 1 else 0) := by
  apply Array.ext
  · simp [Png.generatedDynamicDistLengths, hsize]
  · intro i hleft hright
    simp [Png.generatedDynamicDistLengths, Png.generatedDynamicDistLengthAt, hfreq]

/-- With no distance-1 frequency, generated distance lengths are all zero. This
is the literal-only dynamic-block case accepted by the parser. -/
lemma generatedDynamicDistLengths_eq_zeroShape
    (freqs : Array Nat)
    (hfreq : ¬ 0 < freqs[0]!) :
    Png.generatedDynamicDistLengths freqs =
      Array.replicate freqs.size 0 := by
  apply Array.ext
  · simp [Png.generatedDynamicDistLengths]
  · intro i hleft hright
    simp [Png.generatedDynamicDistLengths, Png.generatedDynamicDistLengthAt, hfreq]

/-- The concrete generated distance table for streams with matches is accepted
by the runtime distance-table builder. -/
lemma buildDynamicDistTable_generatedDistMatchShape_isSome :
    (Png.buildDynamicDistTable
      (Array.ofFn (fun idx : Fin 30 => if idx.val == 0 then 1 else 0))).isSome =
        true := by
  native_decide

/-- Generated distance lengths are always accepted by `buildDynamicDistTable`.
This covers both match-bearing blocks and literal-only dynamic blocks. -/
lemma buildDynamicDistTable_generatedDynamicDistLengths_isSome
    (tokens : Array Png.DeflateToken) :
    (Png.buildDynamicDistTable
      (Png.generatedDynamicDistLengths
        (Png.distSymbolFreqs tokens))).isSome = true := by
  let freqs := Png.distSymbolFreqs tokens
  by_cases hfreq : 0 < freqs[0]!
  · have hshape :
        Png.generatedDynamicDistLengths freqs =
          Array.ofFn (fun idx : Fin 30 => if idx.val == 0 then 1 else 0) :=
      generatedDynamicDistLengths_eq_matchShape freqs
        (by simpa [freqs] using distSymbolFreqs_size tokens) hfreq
    simpa [freqs, hshape] using buildDynamicDistTable_generatedDistMatchShape_isSome
  · have hshape :
        Png.generatedDynamicDistLengths freqs =
          Array.replicate freqs.size 0 :=
      generatedDynamicDistLengths_eq_zeroShape freqs hfreq
    have hall :
        Png.allZeroCodeLengths (Png.generatedDynamicDistLengths freqs) = true := by
      rw [hshape]
      rw [Png.allZeroCodeLengths]
      exact (Array.all_eq_true).2 (by
        intro i hi
        simp)
    unfold Png.buildDynamicDistTable
    cases hmk : Png.mkHuffman (Png.generatedDynamicDistLengths freqs) with
    | none =>
        simp [freqs, hall]
    | some table =>
        simp

/-- Packages generated distance-table validity as an existential table, which
is the form later header/parser proofs need. -/
lemma buildDynamicDistTable_generatedDynamicDistLengths_exists
    (tokens : Array Png.DeflateToken) :
    ∃ distTable,
      Png.buildDynamicDistTable
        (Png.generatedDynamicDistLengths
          (Png.distSymbolFreqs tokens)) = some distTable := by
  have hsome :=
    buildDynamicDistTable_generatedDynamicDistLengths_isSome tokens
  cases h :
      Png.buildDynamicDistTable
        (Png.generatedDynamicDistLengths
          (Png.distSymbolFreqs tokens)) with
  | none =>
      simp [h] at hsome
  | some distTable =>
      exact ⟨distTable, rfl⟩

/-- Counting generated code lengths preserves the count table shape. This is
the canonical-code proof analogue of the frequency-table size lemmas. -/
lemma countCodeLengthsAux_size
    (lengths : Array Nat) (i : Nat) (count : Array Nat) :
    (Png.countCodeLengthsAux lengths i count).size = count.size := by
  rw [Png.countCodeLengthsAux.eq_1]
  by_cases h : i < lengths.size
  · by_cases hlen : 0 < lengths[i]
    · have hrec :=
        countCodeLengthsAux_size lengths (i + 1) (Png.incrementNatAt count lengths[i])
      simp [h, hlen]
      calc
        (Png.countCodeLengthsAux lengths (i + 1)
            (Png.incrementNatAt count lengths[i])).size =
          (Png.incrementNatAt count lengths[i]).size := hrec
        _ = count.size := by simp
    · have hrec := countCodeLengthsAux_size lengths (i + 1) count
      simp [h, hlen, hrec]
  · simp [h]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- If no positive scanned length equals a target bucket, counting code lengths
preserves that bucket. This isolates the zero-shorter-code argument. -/
lemma countCodeLengthsAux_get!_preserve_of_forall_pos_ne
    (lengths : Array Nat) (i idx : Nat) (count : Array Nat)
    (hidx : idx < count.size)
    (hpreserve :
      ∀ j, i ≤ j → (hj : j < lengths.size) →
        0 < lengths[j]'hj → lengths[j]'hj ≠ idx) :
    (Png.countCodeLengthsAux lengths i count)[idx]! = count[idx]! := by
  rw [Png.countCodeLengthsAux.eq_1]
  by_cases h : i < lengths.size
  · by_cases hlen : 0 < lengths[i]
    · have hne : lengths[i] ≠ idx := hpreserve i le_rfl h hlen
      have hidx' : idx < (Png.incrementNatAt count lengths[i]).size := by
        simpa using hidx
      have hrec :=
        countCodeLengthsAux_get!_preserve_of_forall_pos_ne
          lengths (i + 1) idx (Png.incrementNatAt count lengths[i]) hidx'
          (by
            intro j hle hj hpos
            exact hpreserve j (by omega) hj hpos)
      have hinc :
          (Png.incrementNatAt count lengths[i])[idx]! = count[idx]! :=
        incrementNatAt_get!_ne count lengths[i] idx hidx hne
      simp [h, hlen]
      exact hrec.trans hinc
    · have hrec :=
        countCodeLengthsAux_get!_preserve_of_forall_pos_ne
          lengths (i + 1) idx count hidx
          (by
            intro j hle hj hpos
            exact hpreserve j (by omega) hj hpos)
      simp [h, hlen, hrec]
  · simp [h]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Generated literal/length code-length counting leaves every bucket below
the uniform 9-bit length unchanged. This prepares the `nextCode[9] = 0` proof. -/
lemma countCodeLengthsAux_generatedDynamicLitLenLengths_get!_preserve_lt_codeLen
    (freqs : Array Nat) (i idx : Nat) (count : Array Nat)
    (hidx : idx < count.size)
    (hlt : idx < Png.generatedDynamicLitLenCodeLen) :
    (Png.countCodeLengthsAux (Png.generatedDynamicLitLenLengths freqs) i count)[idx]! =
      count[idx]! := by
  exact
    countCodeLengthsAux_get!_preserve_of_forall_pos_ne
      (Png.generatedDynamicLitLenLengths freqs) i idx count hidx
      (by
        intro j _hle hj hpos heq
        have hnine :=
          (generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine freqs j hj).mp hpos
        have hlt9 : idx < 9 := by
          simpa [Png.generatedDynamicLitLenCodeLen] using hlt
        omega)

/-- With the generated initial count table, every bucket below the uniform
literal/length code size is zero after counting. -/
lemma countCodeLengthsAux_generatedDynamicLitLenLengths_get!_lt_codeLen
    (freqs : Array Nat) (idx : Nat)
    (hlt : idx < Png.generatedDynamicLitLenCodeLen) :
    (Png.countCodeLengthsAux
      (Png.generatedDynamicLitLenLengths freqs) 0
      (Array.replicate (Png.generatedDynamicLitLenCodeLen + 1) 0))[idx]! = 0 := by
  let count := Array.replicate (Png.generatedDynamicLitLenCodeLen + 1) 0
  have hidx : idx < count.size := by
    simp [count]
    omega
  calc
    (Png.countCodeLengthsAux
        (Png.generatedDynamicLitLenLengths freqs) 0 count)[idx]! =
      count[idx]! := by
        exact
          countCodeLengthsAux_generatedDynamicLitLenLengths_get!_preserve_lt_codeLen
            freqs 0 idx count hidx hlt
    _ = 0 := by
        rw [getElem!_pos count idx hidx]
        simp [count]

/-- Counting code lengths can increase a bucket by at most the number of
remaining scanned entries. This bounds generated canonical-code assignment. -/
lemma countCodeLengthsAux_get!_le_count_add_remaining
    (lengths : Array Nat) (i idx : Nat) (count : Array Nat)
    (hidx : idx < count.size) :
    (Png.countCodeLengthsAux lengths i count)[idx]! ≤
      count[idx]! + (lengths.size - i) := by
  rw [Png.countCodeLengthsAux.eq_1]
  by_cases h : i < lengths.size
  · by_cases hlen : 0 < lengths[i]
    · have hidx' : idx < (Png.incrementNatAt count lengths[i]).size := by
        simpa using hidx
      have hrec :=
        countCodeLengthsAux_get!_le_count_add_remaining
          lengths (i + 1) idx (Png.incrementNatAt count lengths[i]) hidx'
      have hinc :=
        incrementNatAt_get!_le_succ count lengths[i] idx hidx
      simp [h, hlen]
      omega
    · have hrec :=
        countCodeLengthsAux_get!_le_count_add_remaining
          lengths (i + 1) idx count hidx
      simp [h, hlen]
      omega
  · simp [h]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- The generated 9-bit literal/length bucket contains no more entries than
the generated literal/length table itself. -/
lemma countCodeLengthsAux_generatedDynamicLitLenLengths_get!_codeLen_le_size
    (freqs : Array Nat) :
    let lengths := Png.generatedDynamicLitLenLengths freqs
    let count0 := Array.replicate (Png.generatedDynamicLitLenCodeLen + 1) 0
    let count := Png.countCodeLengthsAux lengths 0 count0
    count[Png.generatedDynamicLitLenCodeLen]! ≤ lengths.size := by
  intro lengths count0 count
  have hidx : Png.generatedDynamicLitLenCodeLen < count0.size := by
    simp [count0]
  have hbound :=
    countCodeLengthsAux_get!_le_count_add_remaining
      lengths 0 Png.generatedDynamicLitLenCodeLen count0 hidx
  have hzero : count0[Png.generatedDynamicLitLenCodeLen]! = 0 := by
    rw [getElem!_pos count0 Png.generatedDynamicLitLenCodeLen hidx]
    simp [count0]
  simpa [count, hzero] using hbound

/-- For generated token streams, the number of assigned 9-bit literal/length
codes fits strictly inside the available 9-bit code space. -/
lemma countCodeLengthsAux_generatedDynamicLitLenLengths_get!_codeLen_lt_codeSpace
    (tokens : Array Png.DeflateToken) :
    let freqs := Png.litLenSymbolFreqs tokens
    let lengths := Png.generatedDynamicLitLenLengths freqs
    let count0 := Array.replicate (Png.generatedDynamicLitLenCodeLen + 1) 0
    let count := Png.countCodeLengthsAux lengths 0 count0
    count[Png.generatedDynamicLitLenCodeLen]! <
      2 ^ Png.generatedDynamicLitLenCodeLen := by
  intro freqs lengths count0 count
  have hle :
      count[Png.generatedDynamicLitLenCodeLen]! ≤ lengths.size := by
    simpa [freqs, lengths, count0, count] using
      countCodeLengthsAux_generatedDynamicLitLenLengths_get!_codeLen_le_size freqs
  have hlt :
      lengths.size < 2 ^ Png.generatedDynamicLitLenCodeLen := by
    simpa [freqs, lengths] using
      generatedDynamicLitLenLengths_size_lt_codeSpace tokens
  omega

/-- Generated literal/length counts make the canonical 9-bit starting code
zero. This is the next-code side of the generated table validity proof. -/
lemma nextCodesAux_generatedDynamicLitLenLengths_get!_codeLen_eq_zero
    (freqs : Array Nat) :
    let lengths := Png.generatedDynamicLitLenLengths freqs
    let count :=
      Png.countCodeLengthsAux lengths 0
        (Array.replicate (Png.generatedDynamicLitLenCodeLen + 1) 0)
    let nextCode0 := Array.replicate (Png.generatedDynamicLitLenCodeLen + 1) 0
    let nextCode :=
      (Png.nextCodesAux count Png.generatedDynamicLitLenCodeLen 1 0 nextCode0).2
    nextCode[Png.generatedDynamicLitLenCodeLen]! = 0 := by
  intro lengths count nextCode0 nextCode
  have h0 : count[0]! = 0 := by
    simpa [count, lengths] using
      countCodeLengthsAux_generatedDynamicLitLenLengths_get!_lt_codeLen freqs 0
        (by simp [Png.generatedDynamicLitLenCodeLen])
  have h1 : count[1]! = 0 := by
    simpa [count, lengths] using
      countCodeLengthsAux_generatedDynamicLitLenLengths_get!_lt_codeLen freqs 1
        (by simp [Png.generatedDynamicLitLenCodeLen])
  have h2 : count[2]! = 0 := by
    simpa [count, lengths] using
      countCodeLengthsAux_generatedDynamicLitLenLengths_get!_lt_codeLen freqs 2
        (by simp [Png.generatedDynamicLitLenCodeLen])
  have h3 : count[3]! = 0 := by
    simpa [count, lengths] using
      countCodeLengthsAux_generatedDynamicLitLenLengths_get!_lt_codeLen freqs 3
        (by simp [Png.generatedDynamicLitLenCodeLen])
  have h4 : count[4]! = 0 := by
    simpa [count, lengths] using
      countCodeLengthsAux_generatedDynamicLitLenLengths_get!_lt_codeLen freqs 4
        (by simp [Png.generatedDynamicLitLenCodeLen])
  have h5 : count[5]! = 0 := by
    simpa [count, lengths] using
      countCodeLengthsAux_generatedDynamicLitLenLengths_get!_lt_codeLen freqs 5
        (by simp [Png.generatedDynamicLitLenCodeLen])
  have h6 : count[6]! = 0 := by
    simpa [count, lengths] using
      countCodeLengthsAux_generatedDynamicLitLenLengths_get!_lt_codeLen freqs 6
        (by simp [Png.generatedDynamicLitLenCodeLen])
  have h7 : count[7]! = 0 := by
    simpa [count, lengths] using
      countCodeLengthsAux_generatedDynamicLitLenLengths_get!_lt_codeLen freqs 7
        (by simp [Png.generatedDynamicLitLenCodeLen])
  have h8 : count[8]! = 0 := by
    simpa [count, lengths] using
      countCodeLengthsAux_generatedDynamicLitLenLengths_get!_lt_codeLen freqs 8
        (by simp [Png.generatedDynamicLitLenCodeLen])
  simp [nextCode, nextCode0, Png.nextCodesAux, Png.generatedDynamicLitLenCodeLen,
    Array.set!, Array.setIfInBounds,
    h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-- Computing canonical next-code values preserves the next-code table shape.
Later generated-payload proofs use this before indexing emitted symbols. -/
lemma nextCodesAux_size
    (count : Array Nat) (maxLen bits code : Nat) (nextCode : Array Nat) :
    (Png.nextCodesAux count maxLen bits code nextCode).2.size = nextCode.size := by
  rw [Png.nextCodesAux.eq_1]
  by_cases h : bits < maxLen + 1
  · let code' := (code + count[bits - 1]!) <<< 1
    have hrec :=
      nextCodesAux_size count maxLen (bits + 1) code'
        (nextCode.set! bits code')
    simp [h]
    calc
      (Png.nextCodesAux count maxLen (bits + 1) code'
          (nextCode.set! bits code')).2.size =
        (nextCode.set! bits code').size := hrec
      _ = nextCode.size := by simp
  · simp [h]
termination_by maxLen + 1 - bits
decreasing_by
  all_goals
    have hlt : bits < maxLen + 1 := h
    exact Nat.sub_lt_sub_left (k := bits) (m := maxLen + 1) (n := bits + 1)
      hlt (Nat.lt_succ_self bits)

/-- Filling canonical reversed codes preserves the output code table shape.
This isolates the final recursive loop used by generated dynamic payloads. -/
lemma fillCanonicalRevCodesAux_size
    (lengths : Array Nat) (i : Nat) (nextCode : Array Nat)
    (revCodes : Array (Nat × Nat)) :
    (Png.fillCanonicalRevCodesAux lengths i nextCode revCodes).size =
      revCodes.size := by
  rw [Png.fillCanonicalRevCodesAux.eq_1]
  by_cases h : i < lengths.size
  · by_cases hlen : 0 < lengths[i]
    · let codeVal := nextCode[lengths[i]]!
      have hrec :=
        fillCanonicalRevCodesAux_size lengths (i + 1)
          (nextCode.set! lengths[i] (codeVal + 1))
          (revCodes.set! i (Png.reverseBits codeVal lengths[i], lengths[i]))
      simp [h, hlen]
      calc
        (Png.fillCanonicalRevCodesAux lengths (i + 1)
            (nextCode.set! lengths[i] (codeVal + 1))
            (revCodes.set! i (Png.reverseBits codeVal lengths[i], lengths[i]))).size =
          (revCodes.set! i (Png.reverseBits codeVal lengths[i], lengths[i])).size := hrec
        _ = revCodes.size := by simp
    · have hrec := fillCanonicalRevCodesAux_size lengths (i + 1) nextCode revCodes
      simp [h, hlen, hrec]
  · simp [h]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Filling later canonical-code slots preserves any earlier target entry. This
is the overwrite-avoidance fact for code-table lookup proofs. -/
lemma fillCanonicalRevCodesAux_get!_of_lt
    (lengths : Array Nat) (i : Nat) (nextCode : Array Nat)
    (revCodes : Array (Nat × Nat)) (target : Nat)
    (htarget : target < revCodes.size)
    (hlt : target < i) :
    (Png.fillCanonicalRevCodesAux lengths i nextCode revCodes)[target]! =
      revCodes[target]! := by
  rw [Png.fillCanonicalRevCodesAux.eq_1]
  by_cases hi : i < lengths.size
  · by_cases hlen : 0 < lengths[i]
    · let codeVal := nextCode[lengths[i]]!
      let revCodes' := revCodes.set! i (Png.reverseBits codeVal lengths[i], lengths[i])
      have htarget' : target < revCodes'.size := by
        simp [revCodes', htarget]
      have hrec :=
        fillCanonicalRevCodesAux_get!_of_lt lengths (i + 1)
          (nextCode.set! lengths[i] (codeVal + 1)) revCodes' target htarget'
          (by omega)
      have hset : revCodes'[target]! = revCodes[target]! := by
        have hne : i ≠ target := by omega
        simpa [revCodes'] using
          getElem!_set!_ne revCodes i target
            (Png.reverseBits codeVal lengths[i], lengths[i]) htarget hne
      simp [hi, hlen]
      exact hrec.trans hset
    · have hrec :=
        fillCanonicalRevCodesAux_get!_of_lt lengths (i + 1)
          nextCode revCodes target htarget (by omega)
      simp [hi, hlen]
      exact hrec
  · simp [hi]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hltLen : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hltLen (Nat.lt_succ_self i)

/-- A positive length entry is written into the canonical reversed-code table
with the same length. This is the generic payload-code availability bridge. -/
lemma fillCanonicalRevCodesAux_get!_snd_of_pos_at
    (lengths : Array Nat) (i : Nat) (nextCode : Array Nat)
    (revCodes : Array (Nat × Nat)) (target : Nat)
    (hle : i ≤ target)
    (htarget : target < lengths.size)
    (hrevSize : revCodes.size = lengths.size)
    (hpos : 0 < lengths[target]!) :
    (Png.fillCanonicalRevCodesAux lengths i nextCode revCodes)[target]!.2 =
      lengths[target]! := by
  rw [Png.fillCanonicalRevCodesAux.eq_1]
  have hi : i < lengths.size := lt_of_le_of_lt hle htarget
  by_cases heq : i = target
  · subst target
    have hposElem : 0 < lengths[i] := by
      simpa [getElem!_pos lengths i hi] using hpos
    let codeVal := nextCode[lengths[i]]!
    let revCodes' := revCodes.set! i (Png.reverseBits codeVal lengths[i], lengths[i])
    have htargetRev' : i < revCodes'.size := by
      simp [revCodes', hrevSize, hi]
    have hpres :=
      fillCanonicalRevCodesAux_get!_of_lt lengths (i + 1)
        (nextCode.set! lengths[i] (codeVal + 1)) revCodes' i htargetRev'
        (Nat.lt_succ_self i)
    have hset :
        revCodes'[i]! =
          (Png.reverseBits codeVal lengths[i], lengths[i]) := by
      have hrevIdx : i < revCodes.size := by
        simpa [hrevSize] using hi
      simpa [revCodes'] using
        getElem!_set!_eq revCodes i
          (Png.reverseBits codeVal lengths[i], lengths[i]) hrevIdx
    simp [hi, hposElem]
    calc
      (Png.fillCanonicalRevCodesAux lengths (i + 1)
          (nextCode.set! lengths[i] (codeVal + 1)) revCodes')[i]!.2 =
          revCodes'[i]!.2 := by
            simpa using congrArg Prod.snd hpres
      _ = lengths[i] := by
            simp [hset]
  · have hltTarget : i < target := Nat.lt_of_le_of_ne hle heq
    by_cases hposCur : 0 < lengths[i]
    · let codeVal := nextCode[lengths[i]]!
      let revCodes' := revCodes.set! i (Png.reverseBits codeVal lengths[i], lengths[i])
      have hrevSize' : revCodes'.size = lengths.size := by
        simp [revCodes', hrevSize]
      have hrec :=
        fillCanonicalRevCodesAux_get!_snd_of_pos_at lengths (i + 1)
          (nextCode.set! lengths[i] (codeVal + 1)) revCodes' target
          (Nat.succ_le_of_lt hltTarget) htarget hrevSize' hpos
      simp [hi, hposCur]
      exact hrec
    · have hrec :=
        fillCanonicalRevCodesAux_get!_snd_of_pos_at lengths (i + 1)
          nextCode revCodes target (Nat.succ_le_of_lt hltTarget)
          htarget hrevSize hpos
      simp [hi, hposCur]
      exact hrec
termination_by target - i
decreasing_by
  all_goals
    have hlt : i < target := hltTarget
    exact Nat.sub_lt_sub_left (k := i) (m := target) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Canonical reversed-code generation preserves the code-length table shape.
This is the top-level shape invariant for generated dynamic Huffman payloads. -/
lemma canonicalRevCodesFromLengths_size (lengths : Array Nat) :
    (Png.canonicalRevCodesFromLengths lengths).size = lengths.size := by
  simp [Png.canonicalRevCodesFromLengths, fillCanonicalRevCodesAux_size]

/-- Canonical reversed-code generation preserves the advertised length for any
positive symbol. Payload writers use this after proving symbol availability. -/
lemma canonicalRevCodesFromLengths_get!_snd_of_pos
    (lengths : Array Nat) (sym : Nat)
    (hsym : sym < lengths.size)
    (hpos : 0 < lengths[sym]!) :
    (Png.canonicalRevCodesFromLengths lengths)[sym]!.2 =
      lengths[sym]! := by
  unfold Png.canonicalRevCodesFromLengths
  exact fillCanonicalRevCodesAux_get!_snd_of_pos_at lengths 0
    (Png.nextCodesAux
      (Png.countCodeLengthsAux lengths 0
        (Array.replicate (Png.maxCodeLenAux lengths 0 0 + 1) 0))
      (Png.maxCodeLenAux lengths 0 0) 1 0
      (Array.replicate (Png.maxCodeLenAux lengths 0 0 + 1) 0)).2
    (Array.replicate lengths.size (0, 0)) sym (Nat.zero_le sym) hsym
    (by simp) hpos

/-- Positive code lengths become positive bit lengths in canonical code tables.
This is the short corollary most generated payload proofs need. -/
lemma canonicalRevCodesFromLengths_get!_snd_pos_of_pos
    (lengths : Array Nat) (sym : Nat)
    (hsym : sym < lengths.size)
    (hpos : 0 < lengths[sym]!) :
    0 < (Png.canonicalRevCodesFromLengths lengths)[sym]!.2 := by
  rw [canonicalRevCodesFromLengths_get!_snd_of_pos lengths sym hsym hpos]
  exact hpos

/-- The generated literal/length code table has the DEFLATE literal/length
shape. This feeds later payload lookup proofs for literals, matches, and EOB. -/
lemma generatedDynamicLitLenCodes_size (tokens : Array Png.DeflateToken) :
    (Png.canonicalRevCodesFromLengths
      (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))).size = 286 := by
  simp [canonicalRevCodesFromLengths_size, generatedDynamicLitLenLengths_size,
    litLenSymbolFreqs_size]

/-- The generated distance code table has the DEFLATE distance shape. This
feeds later payload lookup proofs for distance-1 match tokens. -/
lemma generatedDynamicDistCodes_size (tokens : Array Png.DeflateToken) :
    (Png.canonicalRevCodesFromLengths
      (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))).size = 30 := by
  simp [canonicalRevCodesFromLengths_size, generatedDynamicDistLengths_size,
    distSymbolFreqs_size]

/-- Generated literal code lookup has a positive bit length for every literal
token. This prepares the literal branch of generated payload proofs. -/
lemma generatedDynamicLitLenCodes_literal_len_pos_at
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b) :
    0 <
      (Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths
          (Png.litLenSymbolFreqs tokens)))[b.toNat]!.2 := by
  let lengths := Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hsym : b.toNat < lengths.size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]
    omega
  have hpos : 0 < lengths[b.toNat]! := by
    simpa [lengths] using
      generatedDynamicLitLenLengths_literal_pos_at tokens target b htarget ht
  exact canonicalRevCodesFromLengths_get!_snd_pos_of_pos lengths b.toNat hsym hpos

/-- Generated literal code lookup has the concrete 9-bit length for every
literal token. This links literal payload writes to the generated table shape. -/
lemma generatedDynamicLitLenCodes_literal_len_eq_nine_at
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b) :
    (Png.canonicalRevCodesFromLengths
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqs tokens)))[b.toNat]!.2 = 9 := by
  let lengths := Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hsym : b.toNat < lengths.size := by
    have hb : b.toNat < 256 := UInt8.toNat_lt b
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]
    omega
  have hpos : 0 < lengths[b.toNat]! := by
    simpa [lengths] using
      generatedDynamicLitLenLengths_literal_pos_at tokens target b htarget ht
  have hlen : lengths[b.toNat]! = 9 := by
    simpa [lengths] using
      generatedDynamicLitLenLengths_literal_eq_nine_at tokens target b htarget ht
  rw [canonicalRevCodesFromLengths_get!_snd_of_pos lengths b.toNat hsym hpos]
  exact hlen

/-- Generated match-symbol lookup has a positive bit length for every valid
match token. This prepares the match branch of generated payload proofs. -/
lemma generatedDynamicLitLenCodes_match_len_pos_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    0 <
      (Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths
          (Png.litLenSymbolFreqs tokens)))[(Png.fixedLenMatchInfo len).1]!.2 := by
  let lengths := Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hsym : (Png.fixedLenMatchInfo len).1 < lengths.size := by
    have hfixed := fixedLenMatchInfo_sym_lt_286 len hlen
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]
    omega
  have hpos : 0 < lengths[(Png.fixedLenMatchInfo len).1]! := by
    simpa [lengths] using
      generatedDynamicLitLenLengths_match_pos_at tokens target len htarget ht hlen
  exact canonicalRevCodesFromLengths_get!_snd_pos_of_pos
    lengths (Png.fixedLenMatchInfo len).1 hsym hpos

/-- Generated match-symbol lookup has the concrete 9-bit length for every
valid match token. This links match payload writes to the generated table. -/
lemma generatedDynamicLitLenCodes_match_len_eq_nine_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    (Png.canonicalRevCodesFromLengths
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqs tokens)))[(Png.fixedLenMatchInfo len).1]!.2 = 9 := by
  let lengths := Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hsym : (Png.fixedLenMatchInfo len).1 < lengths.size := by
    have hfixed := fixedLenMatchInfo_sym_lt_286 len hlen
    have hsize : lengths.size = 286 := by
      simp [lengths, generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]
    omega
  have hpos : 0 < lengths[(Png.fixedLenMatchInfo len).1]! := by
    simpa [lengths] using
      generatedDynamicLitLenLengths_match_pos_at tokens target len htarget ht hlen
  have hlenEq : lengths[(Png.fixedLenMatchInfo len).1]! = 9 := by
    simpa [lengths] using
      generatedDynamicLitLenLengths_match_eq_nine_at
        tokens target len htarget ht hlen
  rw [canonicalRevCodesFromLengths_get!_snd_of_pos
    lengths (Png.fixedLenMatchInfo len).1 hsym hpos]
  exact hlenEq

/-- The generated EOB code lookup has a positive bit length. This prepares the
block-termination step for generated payload proofs. -/
lemma generatedDynamicLitLenCodes_eob_len_pos
    (tokens : Array Png.DeflateToken) :
    0 <
      (Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths
          (Png.litLenSymbolFreqs tokens)))[256]!.2 := by
  let lengths := Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hsym : 256 < lengths.size := by
    simpa [lengths] using generatedDynamicLitLenLengths_eob_inBounds tokens
  have hpos : 0 < lengths[256]! := by
    rw [getElem!_pos lengths 256 hsym]
    simpa [lengths] using generatedDynamicLitLenLengths_eob_pos tokens
  exact canonicalRevCodesFromLengths_get!_snd_pos_of_pos lengths 256 hsym hpos

/-- The generated EOB code lookup has the concrete 9-bit length. This is the
exact table-shape fact for generated block termination. -/
lemma generatedDynamicLitLenCodes_eob_len_eq_nine
    (tokens : Array Png.DeflateToken) :
    (Png.canonicalRevCodesFromLengths
      (Png.generatedDynamicLitLenLengths
        (Png.litLenSymbolFreqs tokens)))[256]!.2 = 9 := by
  let lengths := Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hsym : 256 < lengths.size := by
    simpa [lengths] using generatedDynamicLitLenLengths_eob_inBounds tokens
  have hpos : 0 < lengths[256]! := by
    rw [getElem!_pos lengths 256 hsym]
    simpa [lengths] using generatedDynamicLitLenLengths_eob_pos tokens
  have hlen : lengths[256]! = 9 := by
    rw [getElem!_pos lengths 256 hsym]
    simpa [lengths] using generatedDynamicLitLenLengths_eob_eq_nine tokens
  rw [canonicalRevCodesFromLengths_get!_snd_of_pos lengths 256 hsym hpos]
  exact hlen

/-- Generated distance-symbol-zero lookup has a positive bit length when a
match token exists. This prepares distance-1 payload proofs. -/
lemma generatedDynamicDistCodes_zero_len_pos_of_match_at
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len) :
    0 <
      (Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths
          (Png.distSymbolFreqs tokens)))[0]!.2 := by
  let lengths := Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
  have hsym : 0 < lengths.size := by
    simpa [lengths] using generatedDynamicDistLengths_zero_inBounds tokens
  have hpos : 0 < lengths[0]! := by
    simpa [lengths] using
      generatedDynamicDistLengths_zero_get!_pos_of_match_at tokens target len htarget ht
  exact canonicalRevCodesFromLengths_get!_snd_pos_of_pos lengths 0 hsym hpos

/-- The generated dynamic header advertises all 19 code-length-code entries.
This records the concrete table shape used by the header writer. -/
lemma codeLenCodeLengths_size : Png.codeLenCodeLengths.size = 19 := by
  simp [Png.codeLenCodeLengths]

/-- Every generated code-length-code length is valid for DEFLATE. This is the
value-bound side of the generated header's helper Huffman table. -/
lemma codeLenCodeLengths_getElem_le_15
    (idx : Nat) (hidx : idx < Png.codeLenCodeLengths.size) :
    Png.codeLenCodeLengths[idx] ≤ 15 := by
  simp [Png.codeLenCodeLengths]

/-- Every symbol in the generated code-length-code alphabet has a positive
length. The generated header uses a complete 19-symbol helper alphabet. -/
lemma codeLenCodeLengths_get!_pos
    (idx : Nat) (hidx : idx < Png.codeLenCodeLengths.size) :
    0 < Png.codeLenCodeLengths[idx]! := by
  rw [getElem!_pos Png.codeLenCodeLengths idx hidx]
  simp [Png.codeLenCodeLengths]

/-- The generated header's code-length-code table is accepted by the generic
Huffman table builder. This is the first concrete generated-table validity fact. -/
lemma mkHuffman_codeLenCodeLengths_isSome :
    (Png.mkHuffman Png.codeLenCodeLengths).isSome = true := by
  native_decide

/-- The generated code-length-code Huffman table preserves the 19-symbol
alphabet shape used by the dynamic header. -/
lemma generatedCodeLenCodes_size :
    (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths).size = 19 := by
  simp [canonicalRevCodesFromLengths_size, codeLenCodeLengths_size]

/-- Generated code-length-code lookups have positive bit lengths for every
code-length alphabet symbol. This supports generated header RLE proofs. -/
lemma generatedCodeLenCodes_len_pos
    (sym : Nat) (hsym : sym < Png.codeLenCodeLengths.size) :
    0 < (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths)[sym]!.2 := by
  exact canonicalRevCodesFromLengths_get!_snd_pos_of_pos
    Png.codeLenCodeLengths sym hsym
    (codeLenCodeLengths_get!_pos sym hsym)

/-- The DEFLATE code-length alphabet write order has all 19 entries. This is
the header-side shape fact for generated dynamic tables. -/
lemma codeLenOrder_size : Png.codeLenOrder.size = 19 := by
  decide

/-- Every generated header code-length-order entry is a valid code-length
alphabet index. This justifies indexing `codeLenCodeLengths` while writing. -/
lemma codeLenOrder_get!_lt_codeLenCodeLengths_size
    (idx : Nat) (hidx : idx < Png.codeLenOrder.size) :
    Png.codeLenOrder[idx]! < Png.codeLenCodeLengths.size := by
  have hall :
      ∀ idx : Fin Png.codeLenOrder.size,
        Png.codeLenOrder[idx.val]! < Png.codeLenCodeLengths.size := by
    native_decide
  exact hall ⟨idx, hidx⟩

/-- Every symbol named by the DEFLATE code-length order has a generated helper
Huffman code. This is the order-indexed form used by the header writer. -/
lemma generatedCodeLenCodes_order_len_pos
    (idx : Nat) (hidx : idx < Png.codeLenOrder.size) :
    0 <
      (Png.canonicalRevCodesFromLengths
        Png.codeLenCodeLengths)[Png.codeLenOrder[idx]!]!.2 := by
  exact generatedCodeLenCodes_len_pos
    Png.codeLenOrder[idx]!
    (codeLenOrder_get!_lt_codeLenCodeLengths_size idx hidx)

/-- The generated dynamic literal/length count always satisfies the DEFLATE
minimum. This justifies encoding `HLIT = count - 257`. -/
lemma generatedDynamicLitLenCount_ge (litLenLengths : Array Nat) :
    257 ≤ Png.generatedDynamicLitLenCount litLenLengths := by
  unfold Png.generatedDynamicLitLenCount
  exact le_min (by decide) (Nat.le_max_left 257 _)

/-- The generated dynamic literal/length count never exceeds the DEFLATE table
size. This bounds the generated `HLIT` field. -/
lemma generatedDynamicLitLenCount_le (litLenLengths : Array Nat) :
    Png.generatedDynamicLitLenCount litLenLengths ≤ 286 := by
  unfold Png.generatedDynamicLitLenCount
  exact Nat.min_le_left _ _

/-- For generated literal/length tables, the advertised `HLIT` count is inside
the actual generated table. This supports header extraction proofs. -/
lemma generatedDynamicLitLenCount_le_generated_size
    (tokens : Array Png.DeflateToken) :
    Png.generatedDynamicLitLenCount
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)) ≤
      (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)).size := by
  have hle :=
    generatedDynamicLitLenCount_le
      (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
  have hsize :
      (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)).size = 286 := by
    simp [generatedDynamicLitLenLengths_size, litLenSymbolFreqs_size]
  omega

/-- The literal/length header field fits in DEFLATE's 5-bit `HLIT` field for
generated tables. -/
lemma generatedDynamicLitLenCount_sub_le_31
    (tokens : Array Png.DeflateToken) :
    Png.generatedDynamicLitLenCount
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)) - 257 ≤ 31 := by
  have hle :=
    generatedDynamicLitLenCount_le
      (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
  omega

/-- The generated dynamic distance count always satisfies the DEFLATE minimum.
This justifies encoding `HDIST = count - 1`. -/
lemma generatedDynamicDistCount_ge (distLengths : Array Nat) :
    1 ≤ Png.generatedDynamicDistCount distLengths := by
  unfold Png.generatedDynamicDistCount
  exact le_min (by decide) (Nat.le_max_left 1 _)

/-- The generated dynamic distance count never exceeds the DEFLATE distance
table size. This bounds the generated `HDIST` field. -/
lemma generatedDynamicDistCount_le (distLengths : Array Nat) :
    Png.generatedDynamicDistCount distLengths ≤ 30 := by
  unfold Png.generatedDynamicDistCount
  exact Nat.min_le_left _ _

/-- For generated distance tables, the advertised `HDIST` count is inside the
actual generated table. This supports header extraction proofs. -/
lemma generatedDynamicDistCount_le_generated_size
    (tokens : Array Png.DeflateToken) :
    Png.generatedDynamicDistCount
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)) ≤
      (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)).size := by
  have hle :=
    generatedDynamicDistCount_le
      (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))
  have hsize :
      (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)).size = 30 := by
    simp [generatedDynamicDistLengths_size, distSymbolFreqs_size]
  omega

/-- The distance header field fits in DEFLATE's 5-bit `HDIST` field for
generated tables. -/
lemma generatedDynamicDistCount_sub_le_31
    (tokens : Array Png.DeflateToken) :
    Png.generatedDynamicDistCount
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)) - 1 ≤ 31 := by
  have hle :=
    generatedDynamicDistCount_le
      (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))
  omega

/-- The generated dynamic header writes exactly the advertised number of
literal/length and distance code-length entries. -/
lemma generatedDynamicHeaderLengths_size
    (tokens : Array Png.DeflateToken) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let distLengths :=
      Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
    let litLenCount := Png.generatedDynamicLitLenCount litLenLengths
    let distCount := Png.generatedDynamicDistCount distLengths
    ((litLenLengths.extract 0 litLenCount) ++
        (distLengths.extract 0 distCount)).size =
      litLenCount + distCount := by
  intro litLenLengths distLengths litLenCount distCount
  have hlit : litLenCount ≤ litLenLengths.size := by
    simpa [litLenLengths, litLenCount] using
      generatedDynamicLitLenCount_le_generated_size tokens
  have hdist : distCount ≤ distLengths.size := by
    simpa [distLengths, distCount] using
      generatedDynamicDistCount_le_generated_size tokens
  simp [Array.size_append, Array.size_extract, hlit, hdist]

end Lemmas

end Bitmaps
