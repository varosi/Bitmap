import Bitmap.Png

namespace Bitmaps

namespace Png

/-- Records the two dynamic-distance cases accepted by the runtime so later generic proofs can
reason uniformly about normal distance tables and literal-only streams. -/
inductive DynamicDistCase (distLengths : Array Nat) : Huffman -> Prop where
  | nonempty (table : Huffman) (h : mkHuffman distLengths = some table) :
      DynamicDistCase distLengths table
  | empty (h : allZeroCodeLengths distLengths = true) :
      DynamicDistCase distLengths emptyHuffman

/-- Packages the validated tables reconstructed from a dynamic header for later generic decoder
proofs, without committing to one concrete encoder shape. -/
structure DynamicTableSpec where
  litLenLengths : Array Nat
  distLengths : Array Nat
  litLenTable : Huffman
  distTable : Huffman
  litLenOk : mkHuffman litLenLengths = some litLenTable
  distOk : buildDynamicDistTable distLengths = some distTable

/-- Repackages the runtime table-validation boundary into the proof-level record used by later
generic dynamic proofs. -/
def DynamicTableSpec.ofLengths? (litLenLengths distLengths : Array Nat) : Option DynamicTableSpec :=
  match hlit : mkHuffman litLenLengths with
  | none => none
  | some litLenTable =>
      match hdist : buildDynamicDistTable distLengths with
      | none => none
      | some distTable =>
          some
            { litLenLengths := litLenLengths
              distLengths := distLengths
              litLenTable := litLenTable
              distTable := distTable
              litLenOk := hlit
              distOk := hdist }

/-- Keeps the ordinary non-empty distance-table path available without unfolding the runtime
helper at every use site in the generic dynamic proof layer. -/
lemma buildDynamicDistTable_of_mkHuffman
    {distLengths : Array Nat} {table : Huffman}
    (h : mkHuffman distLengths = some table) :
    buildDynamicDistTable distLengths = some table := by
  simp [buildDynamicDistTable, h]

/-- Classifies every successful dynamic-distance build into either a real Huffman table or the
literal-only empty-distance special case accepted by the runtime. -/
lemma buildDynamicDistTable_cases
    {distLengths : Array Nat} {table : Huffman}
    (h : buildDynamicDistTable distLengths = some table) :
    DynamicDistCase distLengths table := by
  unfold buildDynamicDistTable at h
  cases hmk : mkHuffman distLengths with
  | none =>
      by_cases hall : allZeroCodeLengths distLengths = true
      · simp [hall] at h
        cases h
        exact .empty hall
      · simp [hall] at h
  | some built =>
      simp [hmk] at h
      cases h
      exact .nonempty built hmk

/-- Builds the packaged dynamic-table spec directly from the same validation facts used by the
runtime parser. -/
lemma DynamicTableSpec.ofLengths?_mk
    {litLenLengths distLengths : Array Nat} {litLenTable distTable : Huffman}
    (hlit : mkHuffman litLenLengths = some litLenTable)
    (hdist : buildDynamicDistTable distLengths = some distTable) :
    DynamicTableSpec.ofLengths? litLenLengths distLengths =
      some
        { litLenLengths := litLenLengths
          distLengths := distLengths
          litLenTable := litLenTable
          distTable := distTable
          litLenOk := hlit
          distOk := hdist } := by
  simpa [DynamicTableSpec.ofLengths?, hlit, hdist]

/-- Characterizes successful packaged table validation in terms of the underlying runtime table
builders, while keeping the code-length arrays visible. -/
lemma DynamicTableSpec.ofLengths?_eq_some_iff
    {litLenLengths distLengths : Array Nat} {spec : DynamicTableSpec} :
    DynamicTableSpec.ofLengths? litLenLengths distLengths = some spec ↔
      spec.litLenLengths = litLenLengths ∧
      spec.distLengths = distLengths ∧
      mkHuffman litLenLengths = some spec.litLenTable ∧
      buildDynamicDistTable distLengths = some spec.distTable := by
  constructor
  · intro h
    unfold DynamicTableSpec.ofLengths? at h
    split at h <;> try simp at h
    split at h <;> try simp at h
    cases h
    simp_all
  · rintro ⟨rfl, rfl, hlit, hdist⟩
    simpa [DynamicTableSpec.ofLengths?, hlit, hdist]

/-- Any packaged dynamic-table spec still remembers which runtime distance-table case it came
from, including the literal-only empty-distance special case. -/
lemma DynamicTableSpec.distCase (spec : DynamicTableSpec) :
    DynamicDistCase spec.distLengths spec.distTable := by
  exact buildDynamicDistTable_cases spec.distOk

/-- Forgets the stored code-length arrays when a generic dynamic-table parse is viewed through the
runtime `readDynamicTables` interface. -/
def DynamicTableSpec.toReadTablesResult (r : DynamicTableSpec × BitReader) :
    Huffman × Huffman × BitReader :=
  (r.1.litLenTable, r.1.distTable, r.2)

/-- Replays `readDynamicTables` while retaining the validated code-length arrays in
`DynamicTableSpec` for later generic proofs. -/
def readDynamicTablesSpec? (br : BitReader) : Option (DynamicTableSpec × BitReader) := do
  let (hlitBits, br) ←
    if h : br.bitIndex + 5 <= br.data.size * 8 then
      some (br.readBits 5 h)
    else
      none
  let (hdistBits, br) ←
    if h : br.bitIndex + 5 <= br.data.size * 8 then
      some (br.readBits 5 h)
    else
      none
  let (hclenBits, br) ←
    if h : br.bitIndex + 4 <= br.data.size * 8 then
      some (br.readBits 4 h)
    else
      none
  let hlit := hlitBits + 257
  let hdist := hdistBits + 1
  let hclen := hclenBits + 4
  let order : Array Nat := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
  let mut codeLenLengths : Array Nat := Array.replicate 19 0
  let mut brCur := br
  for i in [0:hclen] do
    let (len, br') ←
      if h : brCur.bitIndex + 3 <= brCur.data.size * 8 then
        some (brCur.readBits 3 h)
      else
        none
    codeLenLengths := codeLenLengths.set! order[i]! len
    brCur := br'
  let codeLenTable ← mkHuffman codeLenLengths
  let total := hlit + hdist
  let lengths0 : Array Nat := Array.mkEmpty total
  let (lengths, brNext) ←
    readDynamicTablesLengthsFuel (brCur.data.size * 8 + 1) total codeLenTable brCur lengths0
  if lengths.size != total then
    none
  else
    let litLenLengths := lengths.extract 0 hlit
    let distLengths := lengths.extract hlit (hlit + hdist)
    let spec ← DynamicTableSpec.ofLengths? litLenLengths distLengths
    return (spec, brNext)

/-- Forgetting the stored arrays from the generic parser wrapper recovers exactly the runtime
`readDynamicTables` result. -/
lemma readDynamicTablesSpec?_map (br : BitReader) :
    Option.map DynamicTableSpec.toReadTablesResult (readDynamicTablesSpec? br) =
      readDynamicTables br := by
  unfold readDynamicTablesSpec? readDynamicTables DynamicTableSpec.toReadTablesResult
  simp [DynamicTableSpec.ofLengths?]

/-- Any successful generic dynamic-table parse projects to the corresponding successful runtime
`readDynamicTables` result. -/
lemma readDynamicTablesSpec?_sound
    {br : BitReader} {spec : DynamicTableSpec} {br' : BitReader}
    (h : readDynamicTablesSpec? br = some (spec, br')) :
    readDynamicTables br = some (spec.litLenTable, spec.distTable, br') := by
  have hmap := congrArg (Option.map DynamicTableSpec.toReadTablesResult) h
  rw [readDynamicTablesSpec?_map] at hmap
  simpa [DynamicTableSpec.toReadTablesResult] using hmap

/-- Any successful runtime dynamic-table parse can be lifted back to a generic `DynamicTableSpec`
that still remembers the validated code-length arrays. -/
lemma readDynamicTables_exists_spec
    {br : BitReader} {litLenTable distTable : Huffman} {br' : BitReader}
    (h : readDynamicTables br = some (litLenTable, distTable, br')) :
    ∃ spec,
      readDynamicTablesSpec? br = some (spec, br') ∧
        spec.litLenTable = litLenTable ∧
        spec.distTable = distTable := by
  cases hspec : readDynamicTablesSpec? br with
  | none =>
      have hnone : readDynamicTables br = none := by
        simpa [hspec, DynamicTableSpec.toReadTablesResult] using (readDynamicTablesSpec?_map br)
      rw [h] at hnone
      contradiction
  | some r =>
      rcases r with ⟨spec, br''⟩
      have hmap := readDynamicTablesSpec?_map br
      rw [hspec] at hmap
      simp [DynamicTableSpec.toReadTablesResult] at hmap
      rw [h] at hmap
      rcases hmap with ⟨hlit, hdist, hbr⟩
      subst hbr
      exact ⟨spec, hspec, hlit, hdist⟩

/-- Records one non-terminal payload step accepted by the decoder once the dynamic tables have
already been validated. -/
inductive DynamicPayloadTransition (spec : DynamicTableSpec)
    (br : BitReader) (out : ByteArray) : BitReader → ByteArray → Prop where
  | literal (sym : Nat) (br' : BitReader)
      (hdecode : spec.litLenTable.decode br = some (sym, br'))
      (hlit : sym < 256) :
      DynamicPayloadTransition spec br out br' (out.push (u8 sym))
  | match (sym extra len distSym extraD distance : Nat)
      (br' br'' br''' br'''' : BitReader) (out' : ByteArray)
      (hdecodeSym : spec.litLenTable.decode br = some (sym, br'))
      (hnotLit : ¬ sym < 256)
      (hnotEob : (sym == 256) = false)
      (hsym : 257 ≤ sym ∧ sym ≤ 285)
      (hextra :
        extra =
          Array.getInternal lengthExtra (sym - 257) (by
            have hidxle : sym - 257 ≤ 28 := by omega
            have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
            have hsize : lengthExtra.size = 29 := by decide
            simpa [hsize] using hidxlt))
      (hbits : br'.bitIndex + extra ≤ br'.data.size * 8)
      (hdecodeLen :
        decodeLength sym br' hsym
          (by
            have hbits' : br'.bitIndex +
                lengthExtra[sym - 257]'(by
                  have hidxle : sym - 257 ≤ 28 := by omega
                  have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                  have hsize : lengthExtra.size = 29 := by decide
                  simpa [hsize] using hidxlt) ≤ br'.data.size * 8 := by
              simpa [hextra] using hbits
            simpa using hbits') = (len, br''))
      (hdecodeDistSym : spec.distTable.decode br'' = some (distSym, br'''))
      (hdist : distSym < distBases.size)
      (hextraD :
        extraD =
          Array.getInternal distExtra distSym (by
            have hDistExtraSize : distExtra.size = 30 := by decide
            have hDistBasesSize : distBases.size = 30 := by decide
            simpa [hDistExtraSize, hDistBasesSize] using hdist))
      (hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8)
      (hdecodeDist :
        decodeDistance distSym br''' hdist
          (by
            have hbitsD' : br'''.bitIndex +
                distExtra[distSym]'(by
                  have hDistExtraSize : distExtra.size = 30 := by decide
                  have hDistBasesSize : distBases.size = 30 := by decide
                  simpa [hDistExtraSize, hDistBasesSize] using hdist) ≤ br'''.data.size * 8 := by
              simpa [hextraD] using hbitsD
            simpa using hbitsD') = (distance, br''''))
      (hcopy : copyDistance out distance len = some out') :
      DynamicPayloadTransition spec br out br'''' out'

/-- Records the terminating end-of-block payload step after the dynamic tables have already been
validated. -/
inductive DynamicPayloadFinish (spec : DynamicTableSpec)
    (br : BitReader) (out : ByteArray) : BitReader → Prop where
  | eob (sym : Nat) (br' : BitReader)
      (hdecode : spec.litLenTable.decode br = some (sym, br'))
      (hnotLit : ¬ sym < 256)
      (heob : (sym == 256) = true) :
      DynamicPayloadFinish spec br out br'

/-- Chains validated payload steps into a whole dynamic payload trace ending in EOB. The step
count is used only to justify `decodeCompressedBlockFuel` recursion. -/
inductive DynamicPayloadTrace (spec : DynamicTableSpec) :
    Nat → BitReader → ByteArray → BitReader → ByteArray → Prop where
  | finish {br br' : BitReader} {out : ByteArray}
      (hfinish : DynamicPayloadFinish spec br out br') :
      DynamicPayloadTrace spec 1 br out br' out
  | step {steps : Nat} {br br' br'' : BitReader} {out out' out'' : ByteArray}
      (hstep : DynamicPayloadTransition spec br out br' out')
      (hrest : DynamicPayloadTrace spec steps br' out' br'' out'') :
      DynamicPayloadTrace spec (steps + 1) br out br'' out''

end Png

end Bitmaps
