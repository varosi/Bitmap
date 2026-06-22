import Bitmap.Lemmas.Png.DynamicEncoderDecode
import Bitmap.Lemmas.Png.DynamicBlockProofsPayload

namespace Bitmaps

namespace Lemmas

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-- Names the generated literal/length Huffman table accepted by `mkHuffman`.
This lets the payload proof talk about the same table that the header parser
reconstructs, without unfolding the table builder at every use site. -/
def generatedDynamicLitLenTable (tokens : Array Png.DeflateToken) : Png.Huffman :=
  match Png.mkHuffman
    (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)) with
  | some table => table
  | none => Png.emptyHuffman

/-- Generated literal/length lengths build the named generated table. This
turns the existing `isSome` validity proof into an exact equation for payload
decode lemmas. -/
lemma mkHuffman_generatedDynamicLitLenLengths_eq
    (tokens : Array Png.DeflateToken) :
    Png.mkHuffman
      (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)) =
        some (generatedDynamicLitLenTable tokens) := by
  have hsome :=
    mkHuffman_generatedDynamicLitLenLengths_isSome tokens
  unfold generatedDynamicLitLenTable
  cases h :
      Png.mkHuffman
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)) with
  | none =>
      simp [h] at hsome
  | some table =>
      rfl

/-- Names the generated dynamic distance table accepted by the parser boundary.
The table is empty for literal-only generated streams and non-empty when
distance-1 match tokens are present. -/
def generatedDynamicDistTable (tokens : Array Png.DeflateToken) : Png.Huffman :=
  match Png.buildDynamicDistTable
    (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)) with
  | some table => table
  | none => Png.emptyHuffman

/-- Generated distance lengths build the named generated distance table. This
packages both the match-bearing and literal-only dynamic-block cases. -/
lemma buildDynamicDistTable_generatedDynamicDistLengths_eq
    (tokens : Array Png.DeflateToken) :
    Png.buildDynamicDistTable
      (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)) =
        some (generatedDynamicDistTable tokens) := by
  obtain ⟨distTable, hdist⟩ :=
    buildDynamicDistTable_generatedDynamicDistLengths_exists tokens
  unfold generatedDynamicDistTable
  rw [hdist]

/-- The generated table spec reconstructed from generated lengths contains
exactly the named generated literal/length and distance tables. This is the
payload proof's bridge from header parsing to symbol decoding. -/
lemma generatedDynamicTableSpec_ofLengths?_eq_named
    (tokens : Array Png.DeflateToken) :
    let litLenLengths :=
      Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
    let distLengths :=
      Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
    Png.DynamicTableSpec.ofLengths? litLenLengths distLengths =
      some
        { litLenLengths := litLenLengths
          distLengths := distLengths
          litLenTable := generatedDynamicLitLenTable tokens
          distTable := generatedDynamicDistTable tokens } := by
  intro litLenLengths distLengths
  exact Png.DynamicTableSpec.ofLengths?_mk
    (litLenLengths := litLenLengths) (distLengths := distLengths)
    (litLenTable := generatedDynamicLitLenTable tokens)
    (distTable := generatedDynamicDistTable tokens)
    (by simpa [litLenLengths] using
      mkHuffman_generatedDynamicLitLenLengths_eq tokens)
    (by simpa [distLengths] using
      buildDynamicDistTable_generatedDynamicDistLengths_eq tokens)

/-- Any spec accepted for the generated lengths is definitionally the named
generated table package. This makes later parser-produced witnesses stable
enough for payload replay. -/
lemma generatedDynamicTableSpec_eq_named_of_ofLengths?
    {tokens : Array Png.DeflateToken} {spec : Png.DynamicTableSpec}
    (h :
      Png.DynamicTableSpec.ofLengths?
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)) =
          some spec) :
    spec =
      { litLenLengths :=
          Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
        distLengths :=
          Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens)
        litLenTable := generatedDynamicLitLenTable tokens
        distTable := generatedDynamicDistTable tokens } := by
  have hnamed :=
    generatedDynamicTableSpec_ofLengths?_eq_named tokens
  simp only at hnamed
  rw [h] at hnamed
  injection hnamed

/-- Proof-facing bit width for one generated dynamic payload token. It mirrors
the literal/length code, optional length-extra bits, and distance code emitted
by `writeDynamicPayload`. -/
def dynamicPayloadTokenBitLen
    (litLenCodes distCodes : Array (Nat × Nat)) : Png.DeflateToken → Nat
  | .literal b => litLenCodes[b.toNat]!.2
  | .matchDist1 len =>
      let info := Png.fixedLenMatchInfo len
      litLenCodes[info.1]!.2 + info.2.2 + distCodes[0]!.2

/-- Proof-facing packed bits for one generated dynamic payload token. The low
bits are the literal/length code, followed by match extra bits and distance
code when the token is a distance-1 match. -/
def dynamicPayloadTokenBits
    (litLenCodes distCodes : Array (Nat × Nat)) : Png.DeflateToken → Nat
  | .literal b => litLenCodes[b.toNat]!.1
  | .matchDist1 len =>
      let info := Png.fixedLenMatchInfo len
      let litBits := litLenCodes[info.1]!.1
      let litLen := litLenCodes[info.1]!.2
      let extraBits := info.2.1
      let extraLen := info.2.2
      let distBits := distCodes[0]!.1
      litBits ||| (extraBits <<< litLen) |||
        (distBits <<< (litLen + extraLen))

/-- Proof-facing bit width of the generated dynamic payload terminator. -/
def dynamicPayloadEobBitLen (litLenCodes : Array (Nat × Nat)) : Nat :=
  litLenCodes[256]!.2

/-- Proof-facing packed bits of the generated dynamic payload terminator. -/
def dynamicPayloadEobBits (litLenCodes : Array (Nat × Nat)) : Nat :=
  litLenCodes[256]!.1

/-- Packed little-endian bit stream for generated dynamic payload tokens plus
the final EOB marker. This is the stream-level target for payload replay. -/
def dynamicPayloadStreamBits
    (litLenCodes distCodes : Array (Nat × Nat)) :
    List Png.DeflateToken → Nat
  | [] => dynamicPayloadEobBits litLenCodes
  | token :: tokens =>
      dynamicPayloadTokenBits litLenCodes distCodes token |||
        (dynamicPayloadStreamBits litLenCodes distCodes tokens <<<
          dynamicPayloadTokenBitLen litLenCodes distCodes token)

/-- Total bit width of the generated dynamic payload token stream plus EOB. -/
def dynamicPayloadStreamLen
    (litLenCodes distCodes : Array (Nat × Nat)) :
    List Png.DeflateToken → Nat
  | [] => dynamicPayloadEobBitLen litLenCodes
  | token :: tokens =>
      dynamicPayloadTokenBitLen litLenCodes distCodes token +
        dynamicPayloadStreamLen litLenCodes distCodes tokens

/-- Proof-facing list writer for generated dynamic payload tokens. It mirrors
the runtime payload loop while exposing a structural induction principle. -/
def writeDynamicPayloadToken
    (bw : Png.BitWriter) (litLenCodes distCodes : Array (Nat × Nat)) :
    Png.DeflateToken → Png.BitWriter
  | .literal b =>
      bw.writeRevCode litLenCodes b.toNat
  | .matchDist1 len =>
      let (sym, extraBits, extraLen) := Png.fixedLenMatchInfo len
      let bw := bw.writeRevCode litLenCodes sym
      let bw := bw.writeBitsFast extraBits extraLen
      bw.writeRevCode distCodes 0

/-- Proof-facing list writer for generated dynamic payload tokens. It mirrors
the runtime payload loop while exposing a structural induction principle. -/
def writeDynamicPayloadTokensList
    (bw : Png.BitWriter) (litLenCodes distCodes : Array (Nat × Nat)) :
    List Png.DeflateToken → Png.BitWriter
  | [] => bw.writeRevCode litLenCodes 256
  | token :: tokens =>
      writeDynamicPayloadTokensList
        (writeDynamicPayloadToken bw litLenCodes distCodes token)
        litLenCodes distCodes tokens

/-- The fold produced by Lean's `forIn` elaboration reduces to the
proof-facing recursive list writer. -/
private lemma writeDynamicPayloadTokensList_foldl
    (bw : Png.BitWriter) (tokens : List Png.DeflateToken)
    (litLenCodes distCodes : Array (Nat × Nat)) :
    (List.foldl
        (fun acc token => writeDynamicPayloadToken acc litLenCodes distCodes token)
        bw tokens).writeRevCode litLenCodes 256 =
      writeDynamicPayloadTokensList bw litLenCodes distCodes tokens := by
  induction tokens generalizing bw with
  | nil =>
      simp [writeDynamicPayloadTokensList]
  | cons token tokens ih =>
      simp [writeDynamicPayloadTokensList, ih]

/-- The list `forIn` loop generated by the runtime payload writer reduces to
the proof-facing recursive list writer. -/
private lemma writeDynamicPayloadTokensList_forIn
    (bw : Png.BitWriter) (tokens : List Png.DeflateToken)
    (litLenCodes distCodes : Array (Nat × Nat)) :
    (Id.run <|
      forIn (m := Id) tokens bw fun token r =>
        pure (ForInStep.yield
          (writeDynamicPayloadToken r litLenCodes distCodes token))).writeRevCode
      litLenCodes 256 =
      writeDynamicPayloadTokensList bw litLenCodes distCodes tokens := by
  simpa using
    writeDynamicPayloadTokensList_foldl bw tokens litLenCodes distCodes

end Lemmas

end Bitmaps
