import Bitmap.Lemmas.Png.DynamicEncoderDecode
import Bitmap.Lemmas.Png.DynamicBlockProofsPayload

namespace Bitmaps

namespace Lemmas

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-- Bit reversal is injective inside a fixed-width code space. This prevents
later generated Huffman-table fills from overwriting an earlier row entry. -/
lemma reverseBits_injective_of_lt
    {a b len : Nat} (ha : a < 2 ^ len) (hb : b < 2 ^ len)
    (h : Png.reverseBits a len = Png.reverseBits b len) :
    a = b := by
  calc
    a = Png.reverseBits (Png.reverseBits a len) len := by
          exact (Png.reverseBits_reverseBits a len ha).symm
    _ = Png.reverseBits (Png.reverseBits b len) len := by rw [h]
    _ = b := Png.reverseBits_reverseBits b len hb

/-- Huffman table filling preserves the number of decode rows when it succeeds.
Generated payload decoding uses this to recover concrete row bounds from
`mkHuffman` without unfolding every successful table fill. -/
lemma fillHuffmanTableAux_size_of_some
    (lengths : Array Nat) (i : Nat) (nextCode : Array Nat)
    (table out : Array (Array (Option Nat)))
    (hfill :
      Png.fillHuffmanTableAux lengths i nextCode table = some out) :
    out.size = table.size := by
  rw [Png.fillHuffmanTableAux.eq_1] at hfill
  by_cases hi : i < lengths.size
  · by_cases hlen : lengths[i] > 0
    · let codeVal := nextCode[lengths[i]]!
      by_cases hcode : codeVal >= (1 <<< lengths[i])
      · simp [hi, hlen, codeVal, hcode] at hfill
      · let nextCode' := nextCode.set! lengths[i] (codeVal + 1)
        let rev := Png.reverseBits codeVal lengths[i]
        let row := table[lengths[i]]!
        by_cases hrev : rev >= row.size
        · simp [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev] at hfill
        · let row' := row.set! rev (some i)
          let table' := table.set! lengths[i] row'
          have hfillRec :
              Png.fillHuffmanTableAux lengths (i + 1) nextCode' table' =
                some out := by
            simpa [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev,
              row', table'] using hfill
          have hrec :=
            fillHuffmanTableAux_size_of_some lengths (i + 1) nextCode'
              table' out hfillRec
          calc
            out.size = table'.size := hrec
            _ = table.size := by simp [table']
    · have hrec :=
        fillHuffmanTableAux_size_of_some lengths (i + 1) nextCode table out
          (by simpa [hi, hlen] using hfill)
      exact hrec
  · have hout : table = out := by
      simpa [hi] using hfill
    rw [← hout]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Successful Huffman table filling preserves the width of any existing row.
Generated payload decoding uses this to recover the concrete lookup-row size
after the builder has installed symbol entries. -/
lemma fillHuffmanTableAux_row_size_of_some
    (lengths : Array Nat) (i : Nat) (nextCode : Array Nat)
    (table out : Array (Array (Option Nat))) (rowIdx : Nat)
    (hrow : rowIdx < table.size)
    (hfill :
      Png.fillHuffmanTableAux lengths i nextCode table = some out) :
    out[rowIdx]!.size = table[rowIdx]!.size := by
  rw [Png.fillHuffmanTableAux.eq_1] at hfill
  by_cases hi : i < lengths.size
  · by_cases hlen : lengths[i] > 0
    · let codeVal := nextCode[lengths[i]]!
      by_cases hcode : codeVal >= (1 <<< lengths[i])
      · simp [hi, hlen, codeVal, hcode] at hfill
      · let nextCode' := nextCode.set! lengths[i] (codeVal + 1)
        let rev := Png.reverseBits codeVal lengths[i]
        let row := table[lengths[i]]!
        by_cases hrev : rev >= row.size
        · simp [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev] at hfill
        · let row' := row.set! rev (some i)
          let table' := table.set! lengths[i] row'
          have hfillRec :
              Png.fillHuffmanTableAux lengths (i + 1) nextCode' table' =
                some out := by
            simpa [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev,
              row', table'] using hfill
          have hrow' : rowIdx < table'.size := by
            simpa [table'] using hrow
          have hrec :=
            fillHuffmanTableAux_row_size_of_some lengths (i + 1) nextCode'
              table' out rowIdx hrow' hfillRec
          have htable' : table'[rowIdx]!.size = table[rowIdx]!.size := by
            by_cases heq : lengths[i] = rowIdx
            · subst rowIdx
              simp [table', row', row, hrow]
            · have hset : table'[rowIdx]! = table[rowIdx]! := by
                simpa [table'] using
                  getElem!_set!_ne table (lengths[i]) rowIdx row' hrow heq
              simpa [hset]
          exact hrec.trans htable'
    · have hrec :=
        fillHuffmanTableAux_row_size_of_some lengths (i + 1) nextCode table out
          rowIdx hrow (by simpa [hi, hlen] using hfill)
      exact hrec
  · have hout : table = out := by
      simpa [hi] using hfill
    rw [← hout]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

/-- Uniform Huffman table filling leaves rows other than the uniform code-length
row unchanged. Generated payload decoding uses this to show shorter prefix rows
cannot resolve before the nine-bit literal/length row. -/
lemma fillHuffmanTableAux_uniform_row_eq_of_ne
    (lengths : Array Nat) (i codeLen : Nat) (nextCode : Array Nat)
    (table out : Array (Array (Option Nat))) (rowIdx : Nat)
    (hshape :
      ∀ j (hj : j < lengths.size), i ≤ j →
        0 < lengths[j] → lengths[j] = codeLen)
    (hrowNe : rowIdx ≠ codeLen)
    (hrow : rowIdx < table.size)
    (hfill :
      Png.fillHuffmanTableAux lengths i nextCode table = some out) :
    out[rowIdx]! = table[rowIdx]! := by
  rw [Png.fillHuffmanTableAux.eq_1] at hfill
  by_cases hi : i < lengths.size
  · by_cases hlen : lengths[i] > 0
    · have hlenEq : lengths[i] = codeLen :=
        hshape i hi le_rfl hlen
      let codeVal := nextCode[lengths[i]]!
      by_cases hcode : codeVal >= (1 <<< lengths[i])
      · simp [hi, hlen, codeVal, hcode] at hfill
      · let nextCode' := nextCode.set! lengths[i] (codeVal + 1)
        let rev := Png.reverseBits codeVal lengths[i]
        let row := table[lengths[i]]!
        by_cases hrev : rev >= row.size
        · simp [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev] at hfill
        · let row' := row.set! rev (some i)
          let table' := table.set! lengths[i] row'
          have hfillRec :
              Png.fillHuffmanTableAux lengths (i + 1) nextCode' table' =
                some out := by
            simpa [hi, hlen, codeVal, hcode, nextCode', rev, row, hrev,
              row', table'] using hfill
          have hrow' : rowIdx < table'.size := by
            simpa [table'] using hrow
          have hshape' :
              ∀ j (hj : j < lengths.size), i + 1 ≤ j →
                0 < lengths[j] → lengths[j] = codeLen := by
            intro j hj hle hpos
            exact hshape j hj (by omega) hpos
          have hrec :=
            fillHuffmanTableAux_uniform_row_eq_of_ne lengths (i + 1) codeLen
              nextCode' table' out rowIdx hshape' hrowNe hrow' hfillRec
          have hset : table'[rowIdx]! = table[rowIdx]! := by
            have hne : lengths[i] ≠ rowIdx := by
              intro heq
              exact hrowNe (heq ▸ hlenEq)
            simpa [table'] using
              getElem!_set!_ne table (lengths[i]) rowIdx row' hrow hne
          exact hrec.trans hset
    · have hshape' :
        ∀ j (hj : j < lengths.size), i + 1 ≤ j →
          0 < lengths[j] → lengths[j] = codeLen := by
        intro j hj hle hpos
        exact hshape j hj (by omega) hpos
      have hrec :=
        fillHuffmanTableAux_uniform_row_eq_of_ne lengths (i + 1) codeLen
          nextCode table out rowIdx hshape' hrowNe hrow
          (by simpa [hi, hlen] using hfill)
      exact hrec
  · have hout : table = out := by
      simpa [hi] using hfill
    rw [← hout]
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := hi
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

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

/-- The generated literal/length table has the uniform nine-bit maximum.
Payload decode proofs use this to unfold `Huffman.decode` with fixed fuel. -/
lemma generatedDynamicLitLenTable_maxLen
    (tokens : Array Png.DeflateToken) :
    (generatedDynamicLitLenTable tokens).maxLen = 9 := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode := (Png.nextCodesAux count 9 1 0 (Array.replicate 10 0)).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      simp [hfill] at hmk'
      rw [← hmk']

/-- The generated literal/length decode table has rows for lengths zero
through nine. Payload decode proofs use this for the final nine-bit row. -/
lemma generatedDynamicLitLenTable_table_size
    (tokens : Array Png.DeflateToken) :
    (generatedDynamicLitLenTable tokens).table.size = 10 := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode := (Png.nextCodesAux count 9 1 0 (Array.replicate 10 0)).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      have hsize :=
        fillHuffmanTableAux_size_of_some lengths 0 nextCode init table hfill
      simp [hfill] at hmk'
      rw [← hmk']
      calc
        table.size = init.size := hsize
        _ = 10 := by simp [init, huffmanEmptyTable_size]

/-- The generated literal/length table's nine-bit row has the expected 512
entries. This is the concrete row bound for generated payload symbol lookup. -/
lemma generatedDynamicLitLenTable_row9_size
    (tokens : Array Png.DeflateToken) :
    (generatedDynamicLitLenTable tokens).table[9]!.size = 512 := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode := (Png.nextCodesAux count 9 1 0 (Array.replicate 10 0)).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      have hrow : 9 < init.size := by
        simp [init, huffmanEmptyTable_size]
      have hsize :=
        fillHuffmanTableAux_row_size_of_some lengths 0 nextCode init table 9
          hrow hfill
      simp [hfill] at hmk'
      rw [← hmk']
      calc
        table[9]!.size = init[9]!.size := hsize
        _ = 512 := by
          have hinit := huffmanEmptyTable_get!_size 9 9 le_rfl (by decide)
          simpa [init, Nat.shiftLeft_eq] using hinit

/-- Generated literal/length rows shorter than nine bits are empty. This is
the continuation fact needed before a generated payload symbol resolves. -/
lemma generatedDynamicLitLenTable_short_row_get_none
    (tokens : Array Png.DeflateToken) (rowIdx code : Nat)
    (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 9)
    (hcode : code < (generatedDynamicLitLenTable tokens).table[rowIdx]!.size) :
    (generatedDynamicLitLenTable tokens).table[rowIdx]![code]! = none := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode := (Png.nextCodesAux count 9 1 0 (Array.replicate 10 0)).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      have hshape :
          ∀ j (hj : j < lengths.size), 0 ≤ j →
            0 < lengths[j] → lengths[j] = 9 := by
        intro j hj _hle hpos
        have hnine :
            lengths[j] = 9 := by
          simpa [lengths] using
            (generatedDynamicLitLenLengths_getElem_pos_iff_eq_nine
              (Png.litLenSymbolFreqs tokens) j (by simpa [lengths] using hj)).mp
              (by simpa [lengths] using hpos)
        exact hnine
      have hrowInit : rowIdx < init.size := by
        simp [init, huffmanEmptyTable_size]
        omega
      have hrowNe : rowIdx ≠ 9 := by omega
      have hpres :=
        fillHuffmanTableAux_uniform_row_eq_of_ne lengths 0 9 nextCode init
          table rowIdx hshape hrowNe hrowInit hfill
      simp [hfill] at hmk'
      rw [← hmk'] at hcode ⊢
      have hcodeInit : code < init[rowIdx]!.size := by
        simpa [hpres] using hcode
      rw [hpres]
      have hinitRow :
          init[rowIdx]! =
            Array.replicate (1 <<< rowIdx) (none : Option Nat) := by
        rw [getElem!_pos init rowIdx hrowInit]
        simp [init, Png.huffmanEmptyTable, Nat.ne_of_gt hrowPos]
      rw [hinitRow]
      have hcodeRep :
          code < (Array.replicate (1 <<< rowIdx) (none : Option Nat)).size := by
        simpa [hinitRow] using hcodeInit
      rw [getElem!_pos
        (Array.replicate (1 <<< rowIdx) (none : Option Nat)) code hcodeRep]
      simp

/-- Generated literal/length rows below nine bits keep their initialized row
widths. This supplies the modulo bounds for short-prefix decoder steps. -/
lemma generatedDynamicLitLenTable_short_row_size
    (tokens : Array Png.DeflateToken) (rowIdx : Nat)
    (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 9) :
    (generatedDynamicLitLenTable tokens).table[rowIdx]!.size = 1 <<< rowIdx := by
  let lengths :=
    Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens)
  have hmk :
      Png.mkHuffman lengths =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [lengths] using mkHuffman_generatedDynamicLitLenLengths_eq tokens
  have hmax :
      Png.maxCodeLenAux lengths 0 0 =
        Png.generatedDynamicLitLenCodeLen := by
    simpa [lengths] using
      maxCodeLenAux_generatedDynamicLitLenLengths_eq_codeLen tokens
  let count := Png.countCodeLengthsAux lengths 0 (Array.replicate 10 0)
  let nextCode := (Png.nextCodesAux count 9 1 0 (Array.replicate 10 0)).2
  let init := Png.huffmanEmptyTable 9
  have hmk' :
      (match Png.fillHuffmanTableAux lengths 0 nextCode init with
      | none => none
      | some table => some ({ maxLen := 9, table := table } : Png.Huffman)) =
        some (generatedDynamicLitLenTable tokens) := by
    simpa [Png.mkHuffman, lengths, hmax, Png.generatedDynamicLitLenCodeLen,
      count, nextCode, init] using hmk
  cases hfill : Png.fillHuffmanTableAux lengths 0 nextCode init with
  | none =>
      simp [hfill] at hmk'
  | some table =>
      have hrowInit : rowIdx < init.size := by
        simp [init, huffmanEmptyTable_size]
        omega
      have hsize :=
        fillHuffmanTableAux_row_size_of_some lengths 0 nextCode init table rowIdx
          hrowInit hfill
      simp [hfill] at hmk'
      rw [← hmk']
      calc
        table[rowIdx]!.size = init[rowIdx]!.size := hsize
        _ = 1 <<< rowIdx := by
          exact huffmanEmptyTable_get!_size 9 rowIdx (by omega) hrowPos

/-- Any generated literal/length prefix shorter than nine bits is unresolved.
This is the packed-stream form used by the future `decodeFuel` proof. -/
lemma generatedDynamicLitLenTable_prefix_row_none
    (tokens : Array Png.DeflateToken) (bitsTot rowIdx : Nat)
    (hrowPos : 0 < rowIdx) (hrowLt : rowIdx < 9) :
    (generatedDynamicLitLenTable tokens).table[rowIdx]![bitsTot % 2 ^ rowIdx]! =
      none := by
  have hsize :=
    generatedDynamicLitLenTable_short_row_size tokens rowIdx hrowPos hrowLt
  have hcode :
      bitsTot % 2 ^ rowIdx <
        (generatedDynamicLitLenTable tokens).table[rowIdx]!.size := by
    have hpow : 0 < 2 ^ rowIdx := Nat.pow_pos (by decide : 0 < (2 : Nat))
    have hmod : bitsTot % 2 ^ rowIdx < 2 ^ rowIdx := Nat.mod_lt bitsTot hpow
    simpa [hsize, Nat.shiftLeft_eq] using hmod
  exact generatedDynamicLitLenTable_short_row_get_none tokens rowIdx
    (bitsTot % 2 ^ rowIdx) hrowPos hrowLt hcode

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

/-- Generated payload EOB is emitted with the generated nine-bit
literal/length code. This is the terminal width used by payload traces. -/
lemma dynamicPayloadEobBitLen_generated_eq_nine
    (tokens : Array Png.DeflateToken) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    dynamicPayloadEobBitLen litLenCodes = 9 := by
  intro litLenCodes
  simpa [dynamicPayloadEobBitLen, litLenCodes] using
    generatedDynamicLitLenCodes_eob_len_eq_nine tokens

/-- A generated literal payload token uses the generated nine-bit
literal/length row. This links token frequency collection to the payload
writer's literal branch. -/
lemma dynamicPayloadTokenBitLen_generated_literal_eq_nine_at
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))
    dynamicPayloadTokenBitLen litLenCodes distCodes
      (Png.DeflateToken.literal b) = 9 := by
  intro litLenCodes distCodes
  simpa [dynamicPayloadTokenBitLen, litLenCodes] using
    generatedDynamicLitLenCodes_literal_len_eq_nine_at
      tokens target b htarget ht

/-- A generated match payload token uses a nine-bit literal/length symbol,
the DEFLATE match extra bits, and the generated one-bit distance-zero code. -/
lemma dynamicPayloadTokenBitLen_generated_match_eq
    (tokens : Array Png.DeflateToken) (target len : Nat)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.matchDist1 len)
    (hlen : 3 ≤ len ∧ len ≤ 258) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))
    dynamicPayloadTokenBitLen litLenCodes distCodes
      (Png.DeflateToken.matchDist1 len) =
        9 + (Png.fixedLenMatchInfo len).2.2 + 1 := by
  intro litLenCodes distCodes
  have hlit :=
    generatedDynamicLitLenCodes_match_len_eq_nine_at
      tokens target len htarget ht hlen
  have hdist :=
    generatedDynamicDistCodes_zero_len_eq_one_of_match_at
      tokens target len htarget ht
  simpa [dynamicPayloadTokenBitLen, litLenCodes, distCodes,
    Nat.add_assoc] using congrArg₂ Nat.add hlit (congrArg₂ Nat.add rfl hdist)

/-- Generated payload EOB bits fit in the EOB code width. This is the
terminal code-space guard needed by writer concatenation proofs. -/
lemma dynamicPayloadEobBits_generated_lt_codeSpace
    (tokens : Array Png.DeflateToken) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    dynamicPayloadEobBits litLenCodes <
      2 ^ dynamicPayloadEobBitLen litLenCodes := by
  intro litLenCodes
  have hbits := generatedDynamicLitLenCodes_eob_bits_lt_codeSpace tokens
  have hlen := dynamicPayloadEobBitLen_generated_eq_nine tokens
  simpa [dynamicPayloadEobBits, litLenCodes, hlen] using hbits

/-- Generated literal payload bits fit in the literal token width. This is the
literal branch's code-space guard for payload writer replay. -/
lemma dynamicPayloadTokenBits_generated_literal_lt_codeSpace_at
    (tokens : Array Png.DeflateToken) (target : Nat) (b : UInt8)
    (htarget : target < tokens.size)
    (ht : tokens[target]'htarget = Png.DeflateToken.literal b) :
    let litLenCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicLitLenLengths (Png.litLenSymbolFreqs tokens))
    let distCodes :=
      Png.canonicalRevCodesFromLengths
        (Png.generatedDynamicDistLengths (Png.distSymbolFreqs tokens))
    dynamicPayloadTokenBits litLenCodes distCodes
      (Png.DeflateToken.literal b) <
        2 ^ dynamicPayloadTokenBitLen litLenCodes distCodes
          (Png.DeflateToken.literal b) := by
  intro litLenCodes distCodes
  have hbits :=
    generatedDynamicLitLenCodes_literal_bits_lt_codeSpace_at
      tokens target b htarget ht
  have hcodeLen :=
    generatedDynamicLitLenCodes_literal_len_eq_nine_at
      tokens target b htarget ht
  simpa [dynamicPayloadTokenBits, dynamicPayloadTokenBitLen,
    litLenCodes, distCodes, hcodeLen] using hbits

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
