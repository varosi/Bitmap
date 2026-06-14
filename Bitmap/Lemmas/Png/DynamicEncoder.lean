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

/-- Ranked dynamic literal/length code lengths are never zero. This records the
nonzero branch used when a symbol has positive frequency. -/
lemma rankedDynamicCodeLen_pos (rank : Nat) :
    0 < Png.rankedDynamicCodeLen rank := by
  unfold Png.rankedDynamicCodeLen
  by_cases h0 : rank == 0
  · simp [h0]
  · by_cases h3 : rank < 3
    · simp [h0, h3]
    · by_cases h7 : rank < 7
      · simp [h0, h3, h7]
      · by_cases h15 : rank < 15
        · simp [h0, h3, h7, h15]
        · simp [h0, h3, h7, h15]

/-- Ranked dynamic literal/length code lengths fit in DEFLATE's 15-bit limit.
This is the value bound used by generated table validity proofs. -/
lemma rankedDynamicCodeLen_le_15 (rank : Nat) :
    Png.rankedDynamicCodeLen rank ≤ 15 := by
  unfold Png.rankedDynamicCodeLen
  by_cases h0 : rank == 0
  · simp [h0]
  · by_cases h3 : rank < 3
    · simp [h0, h3]
    · by_cases h7 : rank < 7
      · simp [h0, h3, h7]
      · by_cases h15 : rank < 15
        · simp [h0, h3, h7, h15]
        · simp [h0, h3, h7, h15]

/-- A generated literal/length code-length entry is always a valid DEFLATE code
length. This follows directly from the by-index generator. -/
lemma generatedDynamicLitLenLengthAt_le_15 (freqs : Array Nat) (idx : Nat) :
    Png.generatedDynamicLitLenLengthAt freqs idx ≤ 15 := by
  unfold Png.generatedDynamicLitLenLengthAt
  by_cases h : freqs[idx]! > 0
  · simp [h, rankedDynamicCodeLen_le_15]
  · simp [h]

/-- A positive literal/length frequency produces a positive generated code
length. This bridges frequency availability to generated table availability. -/
lemma generatedDynamicLitLenLengthAt_pos_of_freq
    (freqs : Array Nat) (idx : Nat)
    (hfreq : 0 < freqs[idx]!) :
    0 < Png.generatedDynamicLitLenLengthAt freqs idx := by
  unfold Png.generatedDynamicLitLenLengthAt
  simp [hfreq, rankedDynamicCodeLen_pos]

/-- Generated literal/length code lengths preserve the input frequency table
size, so later header proofs can reason about table bounds. -/
lemma generatedDynamicLitLenLengths_size (freqs : Array Nat) :
    (Png.generatedDynamicLitLenLengths freqs).size = freqs.size := by
  simp [Png.generatedDynamicLitLenLengths]

/-- Every in-bounds generated literal/length code-length entry satisfies
DEFLATE's 15-bit limit. This is the table-level validity shape for `HLIT`. -/
lemma generatedDynamicLitLenLengths_getElem_le_15
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicLitLenLengths freqs).size) :
    (Png.generatedDynamicLitLenLengths freqs)[idx] ≤ 15 := by
  simpa [Png.generatedDynamicLitLenLengths] using
    generatedDynamicLitLenLengthAt_le_15 freqs idx

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

/-- Every in-bounds generated distance code-length entry satisfies DEFLATE's
15-bit limit. This is the table-level validity shape for `HDIST`. -/
lemma generatedDynamicDistLengths_getElem_le_15
    (freqs : Array Nat) (idx : Nat)
    (hidx : idx < (Png.generatedDynamicDistLengths freqs).size) :
    (Png.generatedDynamicDistLengths freqs)[idx] ≤ 15 := by
  simpa [Png.generatedDynamicDistLengths] using
    generatedDynamicDistLengthAt_le_15 freqs idx

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

/-- Canonical reversed-code generation preserves the code-length table shape.
This is the top-level shape invariant for generated dynamic Huffman payloads. -/
lemma canonicalRevCodesFromLengths_size (lengths : Array Nat) :
    (Png.canonicalRevCodesFromLengths lengths).size = lengths.size := by
  simp [Png.canonicalRevCodesFromLengths, fillCanonicalRevCodesAux_size]

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

/-- The generated dynamic header advertises all 19 code-length-code entries.
This records the concrete table shape used by the header writer. -/
lemma codeLenCodeLengths_size : Png.codeLenCodeLengths.size = 19 := by
  simp [Png.codeLenCodeLengths]

/-- The generated code-length-code Huffman table preserves the 19-symbol
alphabet shape used by the dynamic header. -/
lemma generatedCodeLenCodes_size :
    (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths).size = 19 := by
  simp [canonicalRevCodesFromLengths_size, codeLenCodeLengths_size]

/-- The DEFLATE code-length alphabet write order has all 19 entries. This is
the header-side shape fact for generated dynamic tables. -/
lemma codeLenOrder_size : Png.codeLenOrder.size = 19 := by
  decide

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

end Lemmas

end Bitmaps
