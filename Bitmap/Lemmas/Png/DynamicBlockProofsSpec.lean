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

/-- Repackages the runtime table-validation boundary into the proof-level record used by later
generic dynamic proofs. -/
def DynamicTableSpec.ofLengths? (litLenLengths distLengths : Array Nat) : Option DynamicTableSpec :=
  match _hlit : mkHuffman litLenLengths with
  | none => none
  | some litLenTable =>
      match _hdist : buildDynamicDistTable distLengths with
      | none => none
      | some distTable =>
          some
            { litLenLengths := litLenLengths
              distLengths := distLengths
              litLenTable := litLenTable
              distTable := distTable }

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
        have htable : table = emptyHuffman := by
          simpa [hmk, hall] using h.symm
        cases htable
        exact .empty hall
      · simp [hmk, hall] at h
  | some built =>
      have htable : built = table := by
        simpa [hmk] using h
      cases htable
      exact .nonempty table hmk

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
          distTable := distTable } := by
  unfold DynamicTableSpec.ofLengths?
  rw [hlit, hdist]

/-- Binding over `DynamicTableSpec.ofLengths?` and projecting the runtime tables reproduces the
same table pair built directly by the runtime validators. -/
lemma DynamicTableSpec.ofLengths?_bind_tables
    (litLenLengths distLengths : Array Nat) (br : BitReader) :
    (DynamicTableSpec.ofLengths? litLenLengths distLengths).bind
      (fun spec => some (spec.litLenTable, spec.distTable, br)) =
      (mkHuffman litLenLengths).bind fun litLenTable =>
        (buildDynamicDistTable distLengths).bind fun distTable =>
          some (litLenTable, distTable, br) := by
  unfold DynamicTableSpec.ofLengths?
  cases mkHuffman litLenLengths with
  | none =>
      rfl
  | some litLenTable =>
      cases buildDynamicDistTable distLengths with
      | none => rfl
      | some distTable => rfl

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
    simpa using (DynamicTableSpec.ofLengths?_mk (hlit := hlit) (hdist := hdist))

/-- Any packaged dynamic-table spec that came from `DynamicTableSpec.ofLengths?` still remembers
which runtime distance-table case it came from. -/
lemma DynamicTableSpec.distCase_of_ofLengths
    {spec : DynamicTableSpec}
    (h : DynamicTableSpec.ofLengths? spec.litLenLengths spec.distLengths = some spec) :
    DynamicDistCase spec.distLengths spec.distTable := by
  rcases (DynamicTableSpec.ofLengths?_eq_some_iff.mp h) with ⟨_, _, _, hdist⟩
  exact buildDynamicDistTable_cases hdist

/-- Forgets the stored code-length arrays when a generic dynamic-table parse is viewed through the
runtime `readDynamicTables` interface. -/
def DynamicTableSpec.toReadTablesResult (r : DynamicTableSpec × BitReader) :
    Huffman × Huffman × BitReader :=
  (r.1.litLenTable, r.1.distTable, r.2)

/-- Replays `readDynamicTables` through a proof-facing table package. The runtime table reader
still owns all bit-level parsing, including code-length repeat encodings. -/
def readDynamicTablesSpec? (br : BitReader) : Option (DynamicTableSpec × BitReader) := do
  let (litLenTable, distTable, br') ← readDynamicTables br
  return (({ litLenLengths := #[]
             distLengths := #[]
             litLenTable := litLenTable
             distTable := distTable } : DynamicTableSpec),
    br')

/-- Forgetting the stored arrays from the generic parser wrapper recovers exactly the runtime
`readDynamicTables` result. -/
lemma readDynamicTablesSpec?_map (br : BitReader) :
    Option.map DynamicTableSpec.toReadTablesResult (readDynamicTablesSpec? br) =
      readDynamicTables br := by
  cases h : readDynamicTables br with
  | none =>
      simp [readDynamicTablesSpec?, h]
  | some r =>
      rcases r with ⟨litLenTable, distTable, br'⟩
      simp [readDynamicTablesSpec?, h, DynamicTableSpec.toReadTablesResult]

/-- Any successful generic dynamic-table parse projects to the corresponding successful runtime
`readDynamicTables` result. -/
lemma readDynamicTablesSpec?_sound
    {br : BitReader} {spec : DynamicTableSpec} {br' : BitReader}
    (h : readDynamicTablesSpec? br = some (spec, br')) :
    readDynamicTables br = some (spec.litLenTable, spec.distTable, br') := by
  calc
    readDynamicTables br =
        Option.map DynamicTableSpec.toReadTablesResult (readDynamicTablesSpec? br) := by
          symm
          exact readDynamicTablesSpec?_map br
    _ = some (spec.litLenTable, spec.distTable, br') := by
          simp [h, DynamicTableSpec.toReadTablesResult]

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
        calc
          readDynamicTables br =
              Option.map DynamicTableSpec.toReadTablesResult (readDynamicTablesSpec? br) := by
                symm
                exact readDynamicTablesSpec?_map br
          _ = none := by simp [hspec]
      rw [h] at hnone
      contradiction
  | some r =>
      rcases r with ⟨spec, br''⟩
      have hmap : readDynamicTables br = some (spec.litLenTable, spec.distTable, br'') := by
        calc
          readDynamicTables br =
              Option.map DynamicTableSpec.toReadTablesResult (readDynamicTablesSpec? br) := by
                symm
                exact readDynamicTablesSpec?_map br
          _ = some (spec.litLenTable, spec.distTable, br'') := by
                simp [hspec, DynamicTableSpec.toReadTablesResult]
      rw [h] at hmap
      injection hmap with htriple
      cases htriple
      exact ⟨spec, by simp, rfl, rfl⟩

/-- Records one non-terminal payload step accepted by the decoder once the dynamic tables have
already been validated. -/
inductive DynamicPayloadTransition (spec : DynamicTableSpec)
    (br : BitReader) (out : ByteArray) : BitReader → ByteArray → Prop where
  | literal (sym : Nat) (br' : BitReader)
      (hdecode : spec.litLenTable.decode br = some (sym, br'))
      (hlit : sym < 256) :
      DynamicPayloadTransition spec br out br' (out.push (u8 sym))
  | copy (sym extra len distSym extraD distance : Nat)
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

/-- RFC-style classification of the code-length alphabet entries used by dynamic table headers.
It records the repeat width and count without tying the spec to one concrete encoder shape. -/
inductive DynamicCodeLengthSymbol : Nat → Nat → Nat → Prop where
  | literal (len : Nat) (hlen : len ≤ 15) :
      DynamicCodeLengthSymbol len 0 len
  | repeatPrev (extra : Nat) (hextra : extra < 4) :
      DynamicCodeLengthSymbol 16 2 (3 + extra)
  | repeatZeroShort (extra : Nat) (hextra : extra < 8) :
      DynamicCodeLengthSymbol 17 3 (3 + extra)
  | repeatZeroLong (extra : Nat) (hextra : extra < 128) :
      DynamicCodeLengthSymbol 18 7 (11 + extra)

/-- A successful dynamic-table parse, with the proof-level table package retained. This is the
public spec boundary for arbitrary valid dynamic headers, including all repeat encodings. -/
structure DynamicTableReaderSpec (br br' : BitReader) where
  spec : DynamicTableSpec
  parsed : readDynamicTablesSpec? br = some (spec, br')

/-- Public dynamic-table correctness theorem: any table reader spec accepted by
`readDynamicTablesSpec?` projects to the runtime `readDynamicTables` result. -/
lemma dynamicTableReaderSpec_readDynamicTables
    {br br' : BitReader} (h : DynamicTableReaderSpec br br') :
    readDynamicTables br = some (h.spec.litLenTable, h.spec.distTable, br') := by
  exact readDynamicTablesSpec?_sound h.parsed

/-- One dynamic DEFLATE block: the block header chooses `BTYPE=10`, the dynamic tables parse
successfully, and the payload follows the validated payload trace semantics. -/
structure DynamicBlockSpec (final : Bool)
    (br : BitReader) (out : ByteArray) (br' : BitReader) (out' : ByteArray) where
  spec : DynamicTableSpec
  headerReader : BitReader
  payloadReader : BitReader
  steps : Nat
  headerReadable : br.bitIndex + 3 ≤ br.data.size * 8
  headerRead :
    br.readBits 3 headerReadable = ((if final then 5 else 4), headerReader)
  tables : readDynamicTablesSpec? headerReader = some (spec, payloadReader)
  payload : DynamicPayloadTrace spec steps payloadReader out br' out'
  payloadFuel : steps ≤ payloadReader.data.size * 8 + 1

/-- A stream made only of dynamic DEFLATE blocks. Non-final blocks carry `BFINAL=0`; the last
block carries `BFINAL=1`, matching the runtime loop's recursive shape. -/
inductive DynamicDeflateStreamSpec :
    Nat → BitReader → ByteArray → BitReader → ByteArray → Prop where
  | final {br br' : BitReader} {out out' : ByteArray}
      (block : DynamicBlockSpec true br out br' out') :
      DynamicDeflateStreamSpec 1 br out br' out'
  | more {blocks : Nat} {br brMid br' : BitReader} {out outMid out' : ByteArray}
      (block : DynamicBlockSpec false br out brMid outMid)
      (rest : DynamicDeflateStreamSpec blocks brMid outMid br' out') :
      DynamicDeflateStreamSpec (blocks + 1) br out br' out'

/-- The `BitReader` that the public zlib decoder constructs for the deflated payload bytes. -/
def zlibPayloadReader (data : ByteArray) : BitReader :=
  { data := data.extract 2 (data.size - 4)
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide }

/-- A zlib envelope whose deflated payload is described by `DynamicDeflateStreamSpec` and whose
trailer matches the decoded output's Adler-32 checksum. -/
structure ZlibDynamicStreamSpec (data out : ByteArray) (hsize : 2 ≤ data.size) where
  blocks : Nat
  finalReader : BitReader
  headerCheck :
    (((data.get 0 (by omega : 0 < data.size)).toNat <<< 8) +
        (data.get 1 (by omega : 1 < data.size)).toNat) % 31 = 0
  compressionMethod :
    (data.get 0 (by omega : 0 < data.size) &&& (0x0F : UInt8)) = (8 : UInt8)
  noPresetDictionary :
    (data.get 1 (by omega : 1 < data.size) &&& (0x20 : UInt8)) = (0 : UInt8)
  stream :
    DynamicDeflateStreamSpec blocks (zlibPayloadReader data) ByteArray.empty finalReader out
  streamFuel : blocks ≤ (zlibPayloadReader data).data.size * 8 + 1
  adlerBound : finalReader.alignByte.bytePos + 2 + 3 < data.size
  adler :
    readU32BE data (finalReader.alignByte.bytePos + 2) adlerBound = (adler32 out).toNat

end Png

end Bitmaps
