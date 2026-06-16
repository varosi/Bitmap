import Bitmap.Lemmas.Png.DynamicEncoder
import Bitmap.Lemmas.Png.DynamicBlockProofsPayloadBase
import Batteries.Data.Array.Lemmas

namespace Bitmaps

namespace Lemmas

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-- Proof-facing bit width of one generated code-length token: five helper-code
bits plus the DEFLATE extra-bit field. -/
def codeLenTokenBitLen (token : Png.CodeLenToken) : Nat :=
  5 + token.extraLen

/-- Proof-facing packed bits for one generated code-length token. The low five
bits are the helper Huffman code, followed by the token extra bits. -/
def codeLenTokenBits (token : Png.CodeLenToken) : Nat :=
  let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
  codes[token.symbol]!.1 ||| (token.extraBits <<< 5)

/-- Packed little-endian bit stream for a list of generated code-length tokens.
This mirrors the writer order used by `writeCodeLenTokens`. -/
def codeLenTokenStreamBits : List Png.CodeLenToken → Nat
  | [] => 0
  | token :: tokens =>
      codeLenTokenBits token |||
        (codeLenTokenStreamBits tokens <<< codeLenTokenBitLen token)

/-- Total bit width of a generated code-length token list. This is the reader
advance amount paired with `codeLenTokenStreamBits`. -/
def codeLenTokenStreamLen : List Png.CodeLenToken → Nat
  | [] => 0
  | token :: tokens => codeLenTokenBitLen token + codeLenTokenStreamLen tokens

/-- Proof-facing expansion of a list of generated code-length tokens. This is
the list form needed for stream replay against the runtime table reader. -/
def codeLenTokensExpandList? : List Png.CodeLenToken → Array Nat → Option (Array Nat)
  | [], lengths => some lengths
  | token :: tokens, lengths =>
      match Png.CodeLenToken.expand lengths token with
      | none => none
      | some lengths' => codeLenTokensExpandList? tokens lengths'

/-- Proof-facing output count for a generated code-length token list. This
tracks how far the dynamic table reader must advance after replaying tokens. -/
def codeLenTokenListOutputCount : List Png.CodeLenToken → Nat
  | [] => 0
  | token :: tokens =>
      CodeLenTokenOutputCount token + codeLenTokenListOutputCount tokens

/-- Proof-facing list writer for generated code-length tokens. It mirrors the
runtime array writer while making structural induction direct. -/
def writeGeneratedCodeLenTokensList (bw : Png.BitWriter) :
    List Png.CodeLenToken → Png.BitWriter
  | [] => bw
  | token :: tokens =>
      writeGeneratedCodeLenTokensList
        (bw.writeCodeLenToken
          (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths) token)
        tokens

/-- Successful list expansion increases the decoded-length array by the sum of
the token output counts. This is the size invariant for stream replay. -/
lemma codeLenTokensExpandList_size_of_some
    {tokens : List Png.CodeLenToken} {lengths lengths' : Array Nat}
    (h : codeLenTokensExpandList? tokens lengths = some lengths') :
    lengths'.size = lengths.size + codeLenTokenListOutputCount tokens := by
  induction tokens generalizing lengths with
  | nil =>
      simp [codeLenTokensExpandList?, codeLenTokenListOutputCount] at h
      simpa [h, codeLenTokenListOutputCount]
  | cons token tokens ih =>
      simp [codeLenTokensExpandList?] at h
      cases hexpand : Png.CodeLenToken.expand lengths token with
      | none =>
          simp [hexpand] at h
      | some lengths1 =>
          simp [hexpand] at h
          have htail := ih h
          have hhead := codeLenToken_expand_size_of_some hexpand
          simp [codeLenTokenListOutputCount, htail, hhead, Nat.add_assoc]

/-- A nonempty valid token list with successful expansion strictly increases
the decoded-length array. This supplies the reader progress condition. -/
lemma codeLenTokensExpandList_size_gt_of_cons_valid
    {token : Png.CodeLenToken} {tokens : List Png.CodeLenToken}
    {lengths lengths' : Array Nat}
    (hvalid : CodeLenTokenValid token)
    (h : codeLenTokensExpandList? (token :: tokens) lengths = some lengths') :
    lengths.size < lengths'.size := by
  have hsize := codeLenTokensExpandList_size_of_some h
  have hpos : 0 < codeLenTokenListOutputCount (token :: tokens) := by
    have hhead := codeLenTokenOutputCount_pos hvalid
    simp [codeLenTokenListOutputCount]
    omega
  omega

/-- A valid generated code-length token's packed bits fit inside its advertised
bit length. This is the code-space bound needed for stream concatenation. -/
lemma codeLenTokenBits_lt_codeSpace
    {token : Png.CodeLenToken} (hvalid : CodeLenTokenValid token) :
    codeLenTokenBits token < 2 ^ codeLenTokenBitLen token := by
  have hcode := generatedCodeLenCodes_token_bits_lt_codeSpace hvalid
  have hextra := codeLenTokenValid_extraBits_lt_codeSpace hvalid
  have hshift :
      token.extraBits <<< 5 < 2 ^ (token.extraLen + 5) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos 5)).mpr hextra
  have hcodeWide :
      (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths)[token.symbol]!.1 <
        2 ^ (token.extraLen + 5) := by
    exact lt_of_lt_of_le hcode (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hor :
      (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths)[token.symbol]!.1 |||
          (token.extraBits <<< 5) <
        2 ^ (token.extraLen + 5) :=
    Nat.or_lt_two_pow hcodeWide hshift
  simpa [codeLenTokenBits, codeLenTokenBitLen, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using hor

/-- A valid list of generated code-length tokens has packed stream bits that
fit inside the stream's total bit length. -/
lemma codeLenTokenStreamBits_lt_codeSpace
    (tokens : List Png.CodeLenToken)
    (hvalid : ∀ token ∈ tokens, CodeLenTokenValid token) :
    codeLenTokenStreamBits tokens < 2 ^ codeLenTokenStreamLen tokens := by
  induction tokens with
  | nil =>
      simp [codeLenTokenStreamBits, codeLenTokenStreamLen]
  | cons token tokens ih =>
      have hhead : CodeLenTokenValid token := hvalid token (by simp)
      have htailValid : ∀ t ∈ tokens, CodeLenTokenValid t := by
        intro t ht
        exact hvalid t (by simp [ht])
      have hbits := codeLenTokenBits_lt_codeSpace hhead
      have htail := ih htailValid
      have hshift :
          codeLenTokenStreamBits tokens <<< codeLenTokenBitLen token <
            2 ^ (codeLenTokenStreamLen tokens + codeLenTokenBitLen token) := by
        rw [Nat.shiftLeft_eq, Nat.pow_add]
        exact (Nat.mul_lt_mul_right (Nat.two_pow_pos (codeLenTokenBitLen token))).mpr htail
      have hheadWide :
          codeLenTokenBits token <
            2 ^ (codeLenTokenStreamLen tokens + codeLenTokenBitLen token) := by
        exact lt_of_lt_of_le hbits (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
      have hor :
          codeLenTokenBits token |||
              (codeLenTokenStreamBits tokens <<< codeLenTokenBitLen token) <
            2 ^ (codeLenTokenStreamLen tokens + codeLenTokenBitLen token) :=
        Nat.or_lt_two_pow hheadWide hshift
      simpa [codeLenTokenStreamBits, codeLenTokenStreamLen, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hor

/-- Splits a cons token stream into its first token and the remaining packed
tail. This normalizes stream arithmetic for the token-stream induction. -/
lemma codeLenTokenStreamBits_cons_or_rest
    (token : Png.CodeLenToken) (tokens : List Png.CodeLenToken) (restBits : Nat) :
    codeLenTokenStreamBits (token :: tokens) |||
        (restBits <<< codeLenTokenStreamLen (token :: tokens)) =
      codeLenTokenBits token |||
        ((codeLenTokenStreamBits tokens |||
            (restBits <<< codeLenTokenStreamLen tokens)) <<<
          codeLenTokenBitLen token) := by
  simp [codeLenTokenStreamBits, codeLenTokenStreamLen, Nat.shiftLeft_or_distrib,
    Png.shiftLeft_shiftLeft, Nat.or_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]

/-- Reassociates a token prefix so the low five bits are the helper Huffman
code and the following bits start with that token's extra field. -/
lemma codeLenTokenBits_or_tail_eq_code_extra_tail
    (token : Png.CodeLenToken) (tailBits : Nat) :
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let codeBits := codes[token.symbol]!.1
    let extraTail := token.extraBits ||| (tailBits <<< token.extraLen)
    codeLenTokenBits token ||| (tailBits <<< codeLenTokenBitLen token) =
      codeBits ||| (extraTail <<< 5) := by
  intro codes codeBits extraTail
  simp [codeLenTokenBits, codeLenTokenBitLen, extraTail, codeBits, codes,
    Nat.shiftLeft_or_distrib, Png.shiftLeft_shiftLeft, Nat.or_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- One generated code-length token writer is equivalent to writing the
proof-facing packed token bits. This bridges runtime token writes to replay. -/
lemma writeGeneratedCodeLenToken_eq_writeBits
    (bw : Png.BitWriter) {token : Png.CodeLenToken}
    (hvalid : CodeLenTokenValid token) :
    bw.writeCodeLenToken
        (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths) token =
      Png.BitWriter.writeBits bw (codeLenTokenBits token)
        (codeLenTokenBitLen token) := by
  let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
  let codeBits := codes[token.symbol]!.1
  have hcode : codeBits < 2 ^ 5 := by
    simpa [codes, codeBits] using generatedCodeLenCodes_token_bits_lt_codeSpace hvalid
  have hlen : codes[token.symbol]!.2 = 5 := by
    simpa [codes] using generatedCodeLenCodes_token_len_eq_five hvalid
  have hconcat :
      Png.BitWriter.writeBits bw (codeBits ||| (token.extraBits <<< 5))
          (5 + token.extraLen) =
        Png.BitWriter.writeBits
          (Png.BitWriter.writeBits bw codeBits 5)
          token.extraBits token.extraLen := by
    exact Png.writeBits_concat bw codeBits token.extraBits 5 token.extraLen hcode
  simp [Png.BitWriter.writeCodeLenToken, Png.BitWriter.writeCodeLenSymbol,
    Png.BitWriter.writeRevCode, Png.writeBitsFast_eq_writeBits, codeLenTokenBits,
    codeLenTokenBitLen, codes, codeBits, hlen, hconcat.symm]

/-- Writing a generated code-length token list is equivalent to writing its
packed stream bits. This is the writer side of the stream replay theorem. -/
lemma writeGeneratedCodeLenTokensList_eq_writeBits
    (bw : Png.BitWriter) (tokens : List Png.CodeLenToken)
    (hvalid : ∀ token ∈ tokens, CodeLenTokenValid token) :
    writeGeneratedCodeLenTokensList bw tokens =
      Png.BitWriter.writeBits bw (codeLenTokenStreamBits tokens)
        (codeLenTokenStreamLen tokens) := by
  induction tokens generalizing bw with
  | nil =>
      simp [writeGeneratedCodeLenTokensList, codeLenTokenStreamBits,
        codeLenTokenStreamLen]
  | cons token tokens ih =>
      have hhead : CodeLenTokenValid token := hvalid token (by simp)
      have htail : ∀ t ∈ tokens, CodeLenTokenValid t := by
        intro t ht
        exact hvalid t (by simp [ht])
      have htoken :=
        writeGeneratedCodeLenToken_eq_writeBits (bw := bw) (token := token) hhead
      have hbits := codeLenTokenBits_lt_codeSpace hhead
      have htailWrite :=
        ih
          (Png.BitWriter.writeBits bw (codeLenTokenBits token)
            (codeLenTokenBitLen token))
          htail
      have hconcat :
          Png.BitWriter.writeBits bw
              (codeLenTokenBits token |||
                (codeLenTokenStreamBits tokens <<< codeLenTokenBitLen token))
              (codeLenTokenBitLen token + codeLenTokenStreamLen tokens) =
            Png.BitWriter.writeBits
              (Png.BitWriter.writeBits bw (codeLenTokenBits token)
                (codeLenTokenBitLen token))
              (codeLenTokenStreamBits tokens)
              (codeLenTokenStreamLen tokens) := by
        exact Png.writeBits_concat bw (codeLenTokenBits token)
          (codeLenTokenStreamBits tokens)
          (codeLenTokenBitLen token) (codeLenTokenStreamLen tokens) hbits
      simp [writeGeneratedCodeLenTokensList, codeLenTokenStreamBits,
        codeLenTokenStreamLen, htoken, htailWrite, hconcat]

/-- The proof-facing generated token writer is just a left fold over the token
list. This normalizes the runtime array writer after `Array.foldl_toList`. -/
lemma writeGeneratedCodeLenTokensList_eq_foldl
    (bw : Png.BitWriter) (tokens : List Png.CodeLenToken) :
    writeGeneratedCodeLenTokensList bw tokens =
      tokens.foldl
        (fun bw token =>
          bw.writeCodeLenToken
            (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths) token)
        bw := by
  induction tokens generalizing bw with
  | nil =>
      simp [writeGeneratedCodeLenTokensList]
  | cons token tokens ih =>
      simp [writeGeneratedCodeLenTokensList, ih]

/-- The runtime array writer for generated code-length tokens is the same as
the proof-facing list writer over `Array.toList`. This bridges writer shapes. -/
lemma writeCodeLenTokens_generated_eq_list
    (bw : Png.BitWriter) (tokens : Array Png.CodeLenToken) :
    bw.writeCodeLenTokens
        (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths) tokens =
      writeGeneratedCodeLenTokensList bw tokens.toList := by
  simp [Png.BitWriter.writeCodeLenTokens, Array.foldl_toList,
    writeGeneratedCodeLenTokensList_eq_foldl]

/-- Runtime generated code-length token arrays write the same packed bits as
their proof-facing list stream when all tokens are valid. -/
lemma writeCodeLenTokens_generated_eq_writeBits
    (bw : Png.BitWriter) (tokens : Array Png.CodeLenToken)
    (hvalid : ∀ token ∈ tokens.toList, CodeLenTokenValid token) :
    bw.writeCodeLenTokens
        (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths) tokens =
      Png.BitWriter.writeBits bw (codeLenTokenStreamBits tokens.toList)
        (codeLenTokenStreamLen tokens.toList) := by
  rw [writeCodeLenTokens_generated_eq_list]
  exact writeGeneratedCodeLenTokensList_eq_writeBits bw tokens.toList hvalid

/-- Decodes the generated five-bit code-length helper code from a writer-built
stream. This is the Huffman-decode bridge needed before replaying dynamic
header RLE tokens. -/
lemma generatedCodeLenHuffman_decode_readerAt_writeBits_core
    (bw : Png.BitWriter) (bitsTot restLen sym : Nat)
    (hrow5 : generatedCodeLenHuffman.table[5]![bitsTot % 2 ^ 5]! = some sym)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let lenTot := 5 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br5 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 5) bw'.flush
      (by
        have hk : 5 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
    generatedCodeLenHuffman.decode br0 = some (sym, br5) := by
  let lenTot := 5 + restLen
  let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
  let bw1 := Png.BitWriter.writeBits bw bitsTot 1
  let bw2 := Png.BitWriter.writeBits bw bitsTot 2
  let bw3 := Png.BitWriter.writeBits bw bitsTot 3
  let bw4 := Png.BitWriter.writeBits bw bitsTot 4
  let bw5 := Png.BitWriter.writeBits bw bitsTot 5
  let br0 := Png.BitWriter.readerAt bw bw'.flush
    (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
  let br1 := Png.BitWriter.readerAt bw1 bw'.flush
    (by
      have hk : 1 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 1 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 1 hbit)
  let br2 := Png.BitWriter.readerAt bw2 bw'.flush
    (by
      have hk : 2 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 2 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 2 hbit)
  let br3 := Png.BitWriter.readerAt bw3 bw'.flush
    (by
      have hk : 3 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 3 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 3 hbit)
  let br4 := Png.BitWriter.readerAt bw4 bw'.flush
    (by
      have hk : 4 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 4 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 4 hbit)
  let br5 := Png.BitWriter.readerAt bw5 bw'.flush
    (by
      have hk : 5 ≤ lenTot := by omega
      simpa [bw', lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  have hbit1 : bw1.bitPos < 8 := by
    simpa [bw1] using Png.bitPos_lt_8_writeBits bw bitsTot 1 hbit
  have hbit2 : bw2.bitPos < 8 := by
    simpa [bw2] using Png.bitPos_lt_8_writeBits bw bitsTot 2 hbit
  have hbit3 : bw3.bitPos < 8 := by
    simpa [bw3] using Png.bitPos_lt_8_writeBits bw bitsTot 3 hbit
  have hbit4 : bw4.bitPos < 8 := by
    simpa [bw4] using Png.bitPos_lt_8_writeBits bw bitsTot 4 hbit
  have hcur1 : bw1.curClearAbove := by
    simpa [bw1] using Png.curClearAbove_writeBits bw bitsTot 1 hbit hcur
  have hcur2 : bw2.curClearAbove := by
    simpa [bw2] using Png.curClearAbove_writeBits bw bitsTot 2 hbit hcur
  have hcur3 : bw3.curClearAbove := by
    simpa [bw3] using Png.curClearAbove_writeBits bw bitsTot 3 hbit hcur
  have hcur4 : bw4.curClearAbove := by
    simpa [bw4] using Png.curClearAbove_writeBits bw bitsTot 4 hbit hcur
  have hsplit1 : bw' = Png.BitWriter.writeBits bw1 (bitsTot >>> 1) (lenTot - 1) := by
    have hk : 1 + (lenTot - 1) = lenTot := by omega
    simpa [bw', bw1, hk] using
      (Png.writeBits_split bw bitsTot 1 (lenTot - 1))
  have hsplit2 : bw' = Png.BitWriter.writeBits bw2 (bitsTot >>> 2) (lenTot - 2) := by
    have hk : 2 + (lenTot - 2) = lenTot := by omega
    simpa [bw', bw2, hk] using
      (Png.writeBits_split bw bitsTot 2 (lenTot - 2))
  have hsplit3 : bw' = Png.BitWriter.writeBits bw3 (bitsTot >>> 3) (lenTot - 3) := by
    have hk : 3 + (lenTot - 3) = lenTot := by omega
    simpa [bw', bw3, hk] using
      (Png.writeBits_split bw bitsTot 3 (lenTot - 3))
  have hsplit4 : bw' = Png.BitWriter.writeBits bw4 (bitsTot >>> 4) (lenTot - 4) := by
    have hk : 4 + (lenTot - 4) = lenTot := by omega
    simpa [bw', bw4, hk] using
      (Png.writeBits_split bw bitsTot 4 (lenTot - 4))
  have hbound0 : br0.bitIndex + 1 ≤ br0.data.size * 8 := by
    simpa [br0, bw', lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot)
        (k := 1) (by omega) hbit)
  have hbound1 : br1.bitIndex + 1 ≤ br1.data.size * 8 := by
    simpa [br1, bw', hsplit1, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw1) (bits := bitsTot >>> 1)
        (len := lenTot - 1) (k := 1) (by omega) hbit1)
  have hbound2 : br2.bitIndex + 1 ≤ br2.data.size * 8 := by
    simpa [br2, bw', hsplit2, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw2) (bits := bitsTot >>> 2)
        (len := lenTot - 2) (k := 1) (by omega) hbit2)
  have hbound3 : br3.bitIndex + 1 ≤ br3.data.size * 8 := by
    simpa [br3, bw', hsplit3, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw3) (bits := bitsTot >>> 3)
        (len := lenTot - 3) (k := 1) (by omega) hbit3)
  have hbound4 : br4.bitIndex + 1 ≤ br4.data.size * 8 := by
    simpa [br4, bw', hsplit4, lenTot] using
      (Png.readerAt_writeBits_bound (bw := bw4) (bits := bitsTot >>> 4)
        (len := lenTot - 4) (k := 1) (by omega) hbit4)
  have hbr0 : br0.bytePos < br0.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br0 (by omega)
  have hbr1 : br1.bytePos < br1.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br1 (by omega)
  have hbr2 : br2.bytePos < br2.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br2 (by omega)
  have hbr3 : br3.bytePos < br3.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br3 (by omega)
  have hbr4 : br4.bytePos < br4.data.size := by
    exact Png.bytePos_lt_of_bitIndex_lt_dataBits br4 (by omega)
  have hread0 : br0.readBit = (bitsTot % 2, br1) := by
    simpa [br0, br1, bw', lenTot] using
      (Png.readBit_readerAt_writeBits (bw := bw) (bits := bitsTot) (len := lenTot)
        hbit hcur (by omega))
  have hbw2 : Png.BitWriter.writeBit bw1 ((bitsTot >>> 1) % 2) = bw2 := by
    simp [bw1, bw2, Png.BitWriter.writeBits]
  have hread1 : br1.readBit = ((bitsTot >>> 1) % 2, br2) := by
    simpa [br1, br2, bw', hsplit1, hbw2, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw1) (bits := bitsTot >>> 1) (len := lenTot - 1)
        hbit1 hcur1 (by omega))
  have hshift2 : bitsTot >>> 1 >>> 1 = bitsTot >>> 2 := by
    simpa using (Nat.shiftRight_add bitsTot 1 1)
  have hbw3 : Png.BitWriter.writeBit bw2 ((bitsTot >>> 2) % 2) = bw3 := by
    simp [bw2, bw3, Png.BitWriter.writeBits, hshift2]
  have hread2 : br2.readBit = ((bitsTot >>> 2) % 2, br3) := by
    simpa [br2, br3, bw', hsplit2, hbw3, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw2) (bits := bitsTot >>> 2) (len := lenTot - 2)
        hbit2 hcur2 (by omega))
  have hshift3 : bitsTot >>> 1 >>> 1 >>> 1 = bitsTot >>> 3 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 = bitsTot >>> 2 >>> 1 := by simp [hshift2]
      _ = bitsTot >>> 3 := by simpa using (Nat.shiftRight_add bitsTot 2 1)
  have hbw4 : Png.BitWriter.writeBit bw3 ((bitsTot >>> 3) % 2) = bw4 := by
    simp [bw3, bw4, Png.BitWriter.writeBits, hshift3]
  have hread3 : br3.readBit = ((bitsTot >>> 3) % 2, br4) := by
    simpa [br3, br4, bw', hsplit3, hbw4, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw3) (bits := bitsTot >>> 3) (len := lenTot - 3)
        hbit3 hcur3 (by omega))
  have hshift4 : bitsTot >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 4 := by
    calc
      bitsTot >>> 1 >>> 1 >>> 1 >>> 1 = bitsTot >>> 3 >>> 1 := by simp [hshift3]
      _ = bitsTot >>> 4 := by simpa using (Nat.shiftRight_add bitsTot 3 1)
  have hbw5 : Png.BitWriter.writeBit bw4 ((bitsTot >>> 4) % 2) = bw5 := by
    simp [bw4, bw5, Png.BitWriter.writeBits, hshift4]
  have hread4 : br4.readBit = ((bitsTot >>> 4) % 2, br5) := by
    simpa [br4, br5, bw', hsplit4, hbw5, lenTot] using
      (Png.readBit_readerAt_writeBits
        (bw := bw4) (bits := bitsTot >>> 4) (len := lenTot - 4)
        hbit4 hcur4 (by omega))
  have htable1 : 1 < generatedCodeLenHuffman.table.size := by
    rw [generatedCodeLenHuffman_table_size]
    decide
  have htable2 : 2 < generatedCodeLenHuffman.table.size := by
    rw [generatedCodeLenHuffman_table_size]
    decide
  have htable3 : 3 < generatedCodeLenHuffman.table.size := by
    rw [generatedCodeLenHuffman_table_size]
    decide
  have htable4 : 4 < generatedCodeLenHuffman.table.size := by
    rw [generatedCodeLenHuffman_table_size]
    decide
  have htable5 : 5 < generatedCodeLenHuffman.table.size := by
    rw [generatedCodeLenHuffman_table_size]
    decide
  have hrowGet1 :
      generatedCodeLenHuffman.table[1]! =
        Array.getInternal generatedCodeLenHuffman.table 1 htable1 := by
    rw [getElem!_pos generatedCodeLenHuffman.table 1 htable1]
    rfl
  have hrowGet2 :
      generatedCodeLenHuffman.table[2]! =
        Array.getInternal generatedCodeLenHuffman.table 2 htable2 := by
    rw [getElem!_pos generatedCodeLenHuffman.table 2 htable2]
    rfl
  have hrowGet3 :
      generatedCodeLenHuffman.table[3]! =
        Array.getInternal generatedCodeLenHuffman.table 3 htable3 := by
    rw [getElem!_pos generatedCodeLenHuffman.table 3 htable3]
    rfl
  have hrowGet4 :
      generatedCodeLenHuffman.table[4]! =
        Array.getInternal generatedCodeLenHuffman.table 4 htable4 := by
    rw [getElem!_pos generatedCodeLenHuffman.table 4 htable4]
    rfl
  have hrowGet5 :
      generatedCodeLenHuffman.table[5]! =
        Array.getInternal generatedCodeLenHuffman.table 5 htable5 := by
    rw [getElem!_pos generatedCodeLenHuffman.table 5 htable5]
    rfl
  have hsize1 :
      (Array.getInternal generatedCodeLenHuffman.table 1 htable1).size = 2 := by
    simpa [hrowGet1] using generatedCodeLenHuffman_row1_size
  have hsize2 :
      (Array.getInternal generatedCodeLenHuffman.table 2 htable2).size = 4 := by
    simpa [hrowGet2] using generatedCodeLenHuffman_row2_size
  have hsize3 :
      (Array.getInternal generatedCodeLenHuffman.table 3 htable3).size = 8 := by
    simpa [hrowGet3] using generatedCodeLenHuffman_row3_size
  have hsize4 :
      (Array.getInternal generatedCodeLenHuffman.table 4 htable4).size = 16 := by
    simpa [hrowGet4] using generatedCodeLenHuffman_row4_size
  have hsize5 :
      (Array.getInternal generatedCodeLenHuffman.table 5 htable5).size = 32 := by
    simpa [hrowGet5] using generatedCodeLenHuffman_row5_size
  have hcode1 : bitsTot % 2 <
      (Array.getInternal generatedCodeLenHuffman.table 1 htable1).size := by
    have hlt : bitsTot % 2 < 2 := Nat.mod_lt bitsTot (by decide)
    rw [← hrowGet1]
    simpa [generatedCodeLenHuffman_row1_size] using hlt
  have hcode2 : bitsTot % 2 ^ 2 <
      (Array.getInternal generatedCodeLenHuffman.table 2 htable2).size := by
    have hlt : bitsTot % 2 ^ 2 < 4 := by
      simpa using Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 2)
    rw [← hrowGet2]
    simpa [generatedCodeLenHuffman_row2_size] using hlt
  have hcode3 : bitsTot % 2 ^ 3 <
      (Array.getInternal generatedCodeLenHuffman.table 3 htable3).size := by
    have hlt : bitsTot % 2 ^ 3 < 8 := by
      simpa using Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 3)
    rw [← hrowGet3]
    simpa [generatedCodeLenHuffman_row3_size] using hlt
  have hcode4 : bitsTot % 2 ^ 4 <
      (Array.getInternal generatedCodeLenHuffman.table 4 htable4).size := by
    have hlt : bitsTot % 2 ^ 4 < 16 := by
      simpa using Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 4)
    rw [← hrowGet4]
    simpa [generatedCodeLenHuffman_row4_size] using hlt
  have hcode5 : bitsTot % 2 ^ 5 <
      (Array.getInternal generatedCodeLenHuffman.table 5 htable5).size := by
    have hlt : bitsTot % 2 ^ 5 < 32 := by
      simpa using Nat.mod_lt bitsTot (by decide : 0 < 2 ^ 5)
    rw [← hrowGet5]
    simpa [generatedCodeLenHuffman_row5_size] using hlt
  have hrow1 :
      Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 1 htable1)
        (bitsTot % 2) hcode1 = none := by
    have hentry :
        generatedCodeLenHuffman.table[1]![bitsTot % 2]! =
          Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 1 htable1)
            (bitsTot % 2) hcode1 := by
      rw [hrowGet1]
      rw [getElem!_pos (Array.getInternal generatedCodeLenHuffman.table 1 htable1)
        (bitsTot % 2) hcode1]
      rfl
    have hp := generatedCodeLenHuffman_prefix1_row_none bitsTot
    rw [hentry] at hp
    exact hp
  have hrow2 :
      Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 2 htable2)
        (bitsTot % 2 ^ 2) hcode2 = none := by
    have hentry :
        generatedCodeLenHuffman.table[2]![bitsTot % 2 ^ 2]! =
          Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 2 htable2)
            (bitsTot % 2 ^ 2) hcode2 := by
      rw [hrowGet2]
      rw [getElem!_pos (Array.getInternal generatedCodeLenHuffman.table 2 htable2)
        (bitsTot % 2 ^ 2) hcode2]
      rfl
    have hp := generatedCodeLenHuffman_prefix2_row_none bitsTot
    rw [hentry] at hp
    exact hp
  have hrow3 :
      Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 3 htable3)
        (bitsTot % 2 ^ 3) hcode3 = none := by
    have hentry :
        generatedCodeLenHuffman.table[3]![bitsTot % 2 ^ 3]! =
          Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 3 htable3)
            (bitsTot % 2 ^ 3) hcode3 := by
      rw [hrowGet3]
      rw [getElem!_pos (Array.getInternal generatedCodeLenHuffman.table 3 htable3)
        (bitsTot % 2 ^ 3) hcode3]
      rfl
    have hp := generatedCodeLenHuffman_prefix3_row_none bitsTot
    rw [hentry] at hp
    exact hp
  have hrow4 :
      Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 4 htable4)
        (bitsTot % 2 ^ 4) hcode4 = none := by
    have hentry :
        generatedCodeLenHuffman.table[4]![bitsTot % 2 ^ 4]! =
          Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 4 htable4)
            (bitsTot % 2 ^ 4) hcode4 := by
      rw [hrowGet4]
      rw [getElem!_pos (Array.getInternal generatedCodeLenHuffman.table 4 htable4)
        (bitsTot % 2 ^ 4) hcode4]
      rfl
    have hp := generatedCodeLenHuffman_prefix4_row_none bitsTot
    rw [hentry] at hp
    exact hp
  have hrow5' :
      Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 5 htable5)
        (bitsTot % 2 ^ 5) hcode5 = some sym := by
    have hentry :
        generatedCodeLenHuffman.table[5]![bitsTot % 2 ^ 5]! =
          Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 5 htable5)
            (bitsTot % 2 ^ 5) hcode5 := by
      rw [hrowGet5]
      rw [getElem!_pos (Array.getInternal generatedCodeLenHuffman.table 5 htable5)
        (bitsTot % 2 ^ 5) hcode5]
      rfl
    rw [hentry] at hrow5
    exact hrow5
  have hprefix2 :
      bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1) = bitsTot % 2 ^ 2 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 1).symm
  have hprefix3 :
      bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2) = bitsTot % 2 ^ 3 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 2).symm
  have hprefix4 :
      bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3) = bitsTot % 2 ^ 4 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 3).symm
  have hprefix5 :
      bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4) = bitsTot % 2 ^ 5 := by
    simpa using (Png.mod_two_pow_decomp_high bitsTot 4).symm
  have hstep0 :
      generatedCodeLenHuffman.decode br0 =
        Png.Huffman.decodeFuel generatedCodeLenHuffman 4 (bitsTot % 2) 1 br1 := by
    have hcode1' :
        0 ||| ((bitsTot % 2) <<< 0) <
          (Array.getInternal generatedCodeLenHuffman.table 1 htable1).size := by
      simpa using hcode1
    have hrow1' :
        Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 1 htable1)
          (0 ||| ((bitsTot % 2) <<< 0)) hcode1' = none := by
      simpa using hrow1
    unfold Png.Huffman.decode
    rw [generatedCodeLenHuffman_maxLen]
    simpa [hread0] using
      (Png.Huffman.decodeFuel_step_none (h := generatedCodeLenHuffman) (fuel := 4)
        (code := 0) (len := 0) (br := br0) (br' := br1)
        (bit := bitsTot % 2) (hbyte := hbr0) (hread := hread0)
        (htable := htable1) (hcode := hcode1') (hrow := hrow1'))
  have hstep1 :
      Png.Huffman.decodeFuel generatedCodeLenHuffman 4 (bitsTot % 2) 1 br1 =
        Png.Huffman.decodeFuel generatedCodeLenHuffman 3 (bitsTot % 2 ^ 2) 2 br2 := by
    have hcode' :
        bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1) <
          (Array.getInternal generatedCodeLenHuffman.table 2 htable2).size := by
      simpa [hprefix2] using hcode2
    have hrow'' :
        Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 2 htable2)
          (bitsTot % 2 ||| (((bitsTot >>> 1) % 2) <<< 1)) hcode' = none := by
      simpa [hprefix2] using hrow2
    simpa [hprefix2] using
      (Png.Huffman.decodeFuel_step_none (h := generatedCodeLenHuffman) (fuel := 3)
        (code := bitsTot % 2) (len := 1) (br := br1) (br' := br2)
        (bit := (bitsTot >>> 1) % 2) (hbyte := hbr1) (hread := hread1)
        (htable := htable2) (hcode := hcode') (hrow := hrow''))
  have hstep2 :
      Png.Huffman.decodeFuel generatedCodeLenHuffman 3 (bitsTot % 2 ^ 2) 2 br2 =
        Png.Huffman.decodeFuel generatedCodeLenHuffman 2 (bitsTot % 2 ^ 3) 3 br3 := by
    have hcode' :
        bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2) <
          (Array.getInternal generatedCodeLenHuffman.table 3 htable3).size := by
      simpa [hprefix3] using hcode3
    have hrow'' :
        Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 3 htable3)
          (bitsTot % 2 ^ 2 ||| (((bitsTot >>> 2) % 2) <<< 2)) hcode' = none := by
      simpa [hprefix3] using hrow3
    simpa [hprefix3] using
      (Png.Huffman.decodeFuel_step_none (h := generatedCodeLenHuffman) (fuel := 2)
        (code := bitsTot % 2 ^ 2) (len := 2) (br := br2) (br' := br3)
        (bit := (bitsTot >>> 2) % 2) (hbyte := hbr2) (hread := hread2)
        (htable := htable3) (hcode := hcode') (hrow := hrow''))
  have hstep3 :
      Png.Huffman.decodeFuel generatedCodeLenHuffman 2 (bitsTot % 2 ^ 3) 3 br3 =
        Png.Huffman.decodeFuel generatedCodeLenHuffman 1 (bitsTot % 2 ^ 4) 4 br4 := by
    have hcode' :
        bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3) <
          (Array.getInternal generatedCodeLenHuffman.table 4 htable4).size := by
      simpa [hprefix4] using hcode4
    have hrow'' :
        Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 4 htable4)
          (bitsTot % 2 ^ 3 ||| (((bitsTot >>> 3) % 2) <<< 3)) hcode' = none := by
      simpa [hprefix4] using hrow4
    simpa [hprefix4] using
      (Png.Huffman.decodeFuel_step_none (h := generatedCodeLenHuffman) (fuel := 1)
        (code := bitsTot % 2 ^ 3) (len := 3) (br := br3) (br' := br4)
        (bit := (bitsTot >>> 3) % 2) (hbyte := hbr3) (hread := hread3)
        (htable := htable4) (hcode := hcode') (hrow := hrow''))
  have hstep4 :
      Png.Huffman.decodeFuel generatedCodeLenHuffman 1 (bitsTot % 2 ^ 4) 4 br4 =
        some (sym, br5) := by
    have hcode' :
        bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4) <
          (Array.getInternal generatedCodeLenHuffman.table 5 htable5).size := by
      simpa [hprefix5] using hcode5
    have hrow'' :
        Array.getInternal (Array.getInternal generatedCodeLenHuffman.table 5 htable5)
          (bitsTot % 2 ^ 4 ||| (((bitsTot >>> 4) % 2) <<< 4)) hcode' = some sym := by
      simpa [hprefix5] using hrow5'
    simpa [hprefix5] using
      (Png.Huffman.decodeFuel_step_some (h := generatedCodeLenHuffman) (fuel := 0)
        (code := bitsTot % 2 ^ 4) (len := 4) (br := br4) (br' := br5)
        (bit := (bitsTot >>> 4) % 2) (sym := sym) (hbyte := hbr4)
        (hread := hread4) (htable := htable5) (hcode := hcode') (hrow := hrow''))
  calc
    generatedCodeLenHuffman.decode br0 =
        Png.Huffman.decodeFuel generatedCodeLenHuffman 4 (bitsTot % 2) 1 br1 := hstep0
    _ = Png.Huffman.decodeFuel generatedCodeLenHuffman 3 (bitsTot % 2 ^ 2) 2 br2 := hstep1
    _ = Png.Huffman.decodeFuel generatedCodeLenHuffman 2 (bitsTot % 2 ^ 3) 3 br3 := hstep2
    _ = Png.Huffman.decodeFuel generatedCodeLenHuffman 1 (bitsTot % 2 ^ 4) 4 br4 := hstep3
    _ = some (sym, br5) := hstep4

/-- A valid generated code-length token decodes to its symbol from the same
writer-built bit stream used by `writeCodeLenToken`. -/
lemma generatedCodeLenHuffman_decode_token_readerAt_writeBits
    (bw : Png.BitWriter) {token : Png.CodeLenToken} (restBits restLen : Nat)
    (hvalid : CodeLenTokenValid token)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let bitsTot := codes[token.symbol]!.1 ||| (restBits <<< 5)
    let lenTot := 5 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br5 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 5) bw'.flush
      (by
        have hk : 5 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
    generatedCodeLenHuffman.decode br0 = some (token.symbol, br5) := by
  intro codes bitsTot lenTot bw' br0 br5
  have hrow5 :
      generatedCodeLenHuffman.table[5]![bitsTot % 2 ^ 5]! =
        some token.symbol := by
    simpa [bitsTot, codes] using
      (generatedCodeLenHuffman_prefix5_row_some hvalid restBits)
  simpa [bitsTot, lenTot, bw', br0, br5] using
    (generatedCodeLenHuffman_decode_readerAt_writeBits_core
      (bw := bw) (bitsTot := bitsTot) (restLen := restLen) (sym := token.symbol)
      hrow5 hbit hcur)

/-- Folding pushes over a numeric range is the same repeat operation used by
code-length token expansion. This bridges parser loops to token semantics. -/
lemma foldl_pushNat_range'_eq_pushNatRepeat
    (xs : Array Nat) (value start len : Nat) :
    List.foldl (fun acc _ => acc.push value) xs (List.range' start len 1) =
      Png.pushNatRepeat xs value len := by
  induction len generalizing xs start with
  | zero =>
      simp [Png.pushNatRepeat]
  | succ n ih =>
      simp [List.range'_succ, Png.pushNatRepeat, ih]

/-- Monadic `forIn` form of the natural-array repeat loop. This matches the
shape produced inside `readDynamicTablesLengthsFuel`. -/
lemma forIn_pushNat_range'_eq_pushNatRepeat
    (xs : Array Nat) (value start len : Nat) :
    forIn (List.range' start len) xs
        (fun _ acc => some (ForInStep.yield (acc.push value))) =
      some (Png.pushNatRepeat xs value len) := by
  induction len generalizing xs start with
  | zero =>
      simp [Png.pushNatRepeat]
  | succ n ih =>
      simp [List.range'_succ, Png.pushNatRepeat, ih]

/-- The parser's `for _ in [0:n]` repeat loop appends the same entries as
`pushNatRepeat`. This is needed for symbols `16`, `17`, and `18`. -/
lemma idRun_pushNatRange_eq_pushNatRepeat
    (xs : Array Nat) (value len : Nat) :
    (Id.run do
      let mut xs := xs
      for _ in [0:len] do
        xs := xs.push value
      return xs) = Png.pushNatRepeat xs value len := by
  simpa [Std.Legacy.Range.forIn_eq_forIn_range'] using
    (foldl_pushNat_range'_eq_pushNatRepeat xs value 0 len)

/-- Unfolds one literal branch of the generated code-length table reader once
the generated helper Huffman decode has produced a literal length. -/
lemma readDynamicTablesLengthsFuel_step_literal_generated
    (fuel total sym : Nat) (br br' : Png.BitReader) (lengths : Array Nat)
    (hsize : lengths.size < total)
    (hdecode : generatedCodeLenHuffman.decode br = some (sym, br'))
    (hsym : sym ≤ 15) :
    Png.readDynamicTablesLengthsFuel (fuel + 1) total generatedCodeLenHuffman br lengths =
      Png.readDynamicTablesLengthsFuel fuel total generatedCodeLenHuffman br'
        (lengths.push sym) := by
  have hge : ¬ total ≤ lengths.size := Nat.not_le_of_lt hsize
  simp [Png.readDynamicTablesLengthsFuel, hge, hdecode, hsym]

/-- Unfolds one previous-length repeat branch of the generated code-length
reader. This connects symbol `16` and its two extra bits to `pushNatRepeat`. -/
lemma readDynamicTablesLengthsFuel_step_repeatPrev_generated
    (fuel total extra : Nat) (br brSym brExtra : Png.BitReader)
    (lengths : Array Nat)
    (hsize : lengths.size < total)
    (hnonempty : lengths.size ≠ 0)
    (hdecode : generatedCodeLenHuffman.decode br = some (16, brSym))
    (hbound : brSym.bitIndex + 2 ≤ brSym.data.size * 8)
    (hread : brSym.readBits 2 hbound = (extra, brExtra)) :
    Png.readDynamicTablesLengthsFuel (fuel + 1) total generatedCodeLenHuffman br lengths =
      Png.readDynamicTablesLengthsFuel fuel total generatedCodeLenHuffman brExtra
        (Png.pushNatRepeat lengths lengths[lengths.size - 1]! (3 + extra)) := by
  have hge : ¬ total ≤ lengths.size := Nat.not_le_of_lt hsize
  have hreadAny :
      ∀ h : brSym.bitIndex + 2 ≤ brSym.data.size * 8,
        brSym.readBits 2 h = (extra, brExtra) := by
    intro h
    simpa using hread
  simp [Png.readDynamicTablesLengthsFuel, hge, hdecode, hnonempty, hbound,
    hreadAny, idRun_pushNatRange_eq_pushNatRepeat]
  rw [forIn_pushNat_range'_eq_pushNatRepeat]
  simp

/-- Unfolds one short zero-repeat branch of the generated code-length reader.
This connects symbol `17` and its three extra bits to `pushNatRepeat`. -/
lemma readDynamicTablesLengthsFuel_step_repeatZeroShort_generated
    (fuel total extra : Nat) (br brSym brExtra : Png.BitReader)
    (lengths : Array Nat)
    (hsize : lengths.size < total)
    (hdecode : generatedCodeLenHuffman.decode br = some (17, brSym))
    (hbound : brSym.bitIndex + 3 ≤ brSym.data.size * 8)
    (hread : brSym.readBits 3 hbound = (extra, brExtra)) :
    Png.readDynamicTablesLengthsFuel (fuel + 1) total generatedCodeLenHuffman br lengths =
      Png.readDynamicTablesLengthsFuel fuel total generatedCodeLenHuffman brExtra
        (Png.pushNatRepeat lengths 0 (3 + extra)) := by
  have hge : ¬ total ≤ lengths.size := Nat.not_le_of_lt hsize
  have hreadAny :
      ∀ h : brSym.bitIndex + 3 ≤ brSym.data.size * 8,
        brSym.readBits 3 h = (extra, brExtra) := by
    intro h
    simpa using hread
  simp [Png.readDynamicTablesLengthsFuel, hge, hdecode, hbound, hreadAny,
    idRun_pushNatRange_eq_pushNatRepeat]
  rw [forIn_pushNat_range'_eq_pushNatRepeat]
  simp

/-- Unfolds one long zero-repeat branch of the generated code-length reader.
This connects symbol `18` and its seven extra bits to `pushNatRepeat`. -/
lemma readDynamicTablesLengthsFuel_step_repeatZeroLong_generated
    (fuel total extra : Nat) (br brSym brExtra : Png.BitReader)
    (lengths : Array Nat)
    (hsize : lengths.size < total)
    (hdecode : generatedCodeLenHuffman.decode br = some (18, brSym))
    (hbound : brSym.bitIndex + 7 ≤ brSym.data.size * 8)
    (hread : brSym.readBits 7 hbound = (extra, brExtra)) :
    Png.readDynamicTablesLengthsFuel (fuel + 1) total generatedCodeLenHuffman br lengths =
      Png.readDynamicTablesLengthsFuel fuel total generatedCodeLenHuffman brExtra
        (Png.pushNatRepeat lengths 0 (11 + extra)) := by
  have hge : ¬ total ≤ lengths.size := Nat.not_le_of_lt hsize
  have hreadAny :
      ∀ h : brSym.bitIndex + 7 ≤ brSym.data.size * 8,
        brSym.readBits 7 h = (extra, brExtra) := by
    intro h
    simpa using hread
  simp [Png.readDynamicTablesLengthsFuel, hge, hdecode, hbound, hreadAny,
    idRun_pushNatRange_eq_pushNatRepeat]
  rw [forIn_pushNat_range'_eq_pushNatRepeat]
  simp

/-- Writing only the first five bits of a packed generated code-length token
is the same as writing its generated helper Huffman code. -/
lemma generatedCodeLenToken_writeBits_code_prefix
    (bw : Png.BitWriter) {token : Png.CodeLenToken} (tailBits : Nat)
    (hvalid : CodeLenTokenValid token) :
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let codeBits := codes[token.symbol]!.1
    Png.BitWriter.writeBits bw (codeBits ||| (tailBits <<< 5)) 5 =
      Png.BitWriter.writeBits bw codeBits 5 := by
  intro codes codeBits
  exact Png.writeBits_or_shift_tail bw codeBits tailBits 5
    (generatedCodeLenCodes_token_bits_lt_codeSpace hvalid)

/-- Splits a packed generated code-length token stream after the five-bit
helper code. The remaining writer input starts with the token extra bits. -/
lemma generatedCodeLenToken_writeBits_concat_code_tail
    (bw : Png.BitWriter) {token : Png.CodeLenToken} (tailBits tailLen : Nat)
    (hvalid : CodeLenTokenValid token) :
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let codeBits := codes[token.symbol]!.1
    let bitsTot := codeBits ||| (tailBits <<< 5)
    Png.BitWriter.writeBits bw bitsTot (5 + tailLen) =
      Png.BitWriter.writeBits (Png.BitWriter.writeBits bw bitsTot 5)
        tailBits tailLen := by
  intro codes codeBits bitsTot
  have hprefix :
      Png.BitWriter.writeBits bw bitsTot 5 =
        Png.BitWriter.writeBits bw codeBits 5 := by
    simpa [bitsTot, codes, codeBits] using
      (generatedCodeLenToken_writeBits_code_prefix
        (bw := bw) (token := token) (tailBits := tailBits) hvalid)
  have hconcat :
      Png.BitWriter.writeBits bw bitsTot (5 + tailLen) =
        Png.BitWriter.writeBits (Png.BitWriter.writeBits bw codeBits 5)
          tailBits tailLen := by
    simpa [bitsTot] using
      (Png.writeBits_concat bw codeBits tailBits 5 tailLen
        (generatedCodeLenCodes_token_bits_lt_codeSpace hvalid))
  simpa [hprefix] using hconcat

/-- Reader equality from equal writer positions and equal backing data. This is
the transport helper used when `writeBits_split` changes the proof objects. -/
lemma readerAt_eq_of_eqs
    {bw1 bw2 : Png.BitWriter} {data1 data2 : ByteArray}
    (hbw : bw1 = bw2) (hdata : data1 = data2)
    (hflush1 : bw1.flush.size ≤ data1.size) (hflush2 : bw2.flush.size ≤ data2.size)
    (hbit1 : bw1.bitPos < 8) (hbit2 : bw2.bitPos < 8) :
    Png.BitWriter.readerAt bw1 data1 hflush1 hbit1 =
      Png.BitWriter.readerAt bw2 data2 hflush2 hbit2 := by
  subst hbw
  subst hdata
  apply Png.BitReader.ext <;> simp [Png.BitWriter.readerAt]

/-- Reads the extra-bit portion of a generated code-length token from the
packed token stream after the five-bit helper code has already been consumed. -/
lemma readCodeLenTokenExtraBits_readerAt_packed
    (bw : Png.BitWriter) {token : Png.CodeLenToken} (restBits restLen : Nat)
    (hvalid : CodeLenTokenValid token)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let codeBits := codes[token.symbol]!.1
    let tailBits := token.extraBits ||| (restBits <<< token.extraLen)
    let bitsTot := codeBits ||| (tailBits <<< 5)
    let bwCode := Png.BitWriter.writeBits bw bitsTot 5
    let tailLen := token.extraLen + restLen
    let bwTail' := Png.BitWriter.writeBits bwCode tailBits tailLen
    let brCode := Png.BitWriter.readerAt bwCode bwTail'.flush
      (Png.flush_size_writeBits_le bwCode tailBits tailLen)
      (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
    brCode.readBits token.extraLen
        (by
          have hk : token.extraLen ≤ tailLen := by omega
          simpa [brCode, bwTail', tailLen] using
            (Png.readerAt_writeBits_bound
              (bw := bwCode) (bits := tailBits) (len := tailLen)
              (k := token.extraLen) hk
              (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit))) =
      (token.extraBits,
        Png.BitWriter.readerAt (Png.BitWriter.writeBits bwCode tailBits token.extraLen)
          bwTail'.flush
          (by
            have hk : token.extraLen ≤ tailLen := by omega
            simpa [tailLen] using
              (Png.flush_size_writeBits_prefix bwCode tailBits token.extraLen tailLen hk))
          (Png.bitPos_lt_8_writeBits bwCode tailBits token.extraLen
            (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit))) := by
  intro codes codeBits tailBits bitsTot bwCode tailLen bwTail' brCode
  have hread :=
    readCodeLenTokenExtraBits_readerAt_writeBits_prefix
      (bw := bwCode) (token := token) (restBits := restBits) (restLen := restLen)
      hvalid
      (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
      (Png.curClearAbove_writeBits bw bitsTot 5 hbit hcur)
  simpa [tailBits, tailLen, bwTail'] using hread

/-- Full-stream form of `readCodeLenTokenExtraBits_readerAt_packed`. It
transports the post-code tail read back to the original packed token writer. -/
lemma readCodeLenTokenExtraBits_readerAt_full_packed
    (bw : Png.BitWriter) {token : Png.CodeLenToken} (restBits restLen : Nat)
    (hvalid : CodeLenTokenValid token)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let codeBits := codes[token.symbol]!.1
    let tailBits := token.extraBits ||| (restBits <<< token.extraLen)
    let bitsTot := codeBits ||| (tailBits <<< 5)
    let lenTot := 5 + (token.extraLen + restLen)
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let bwCode := Png.BitWriter.writeBits bw bitsTot 5
    let brCode := Png.BitWriter.readerAt bwCode bw'.flush
      (by
        have hk : 5 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
    brCode.readBits token.extraLen
        (by
          let tailLen := token.extraLen + restLen
          let bwTail' := Png.BitWriter.writeBits bwCode tailBits tailLen
          have htailShift : bitsTot >>> 5 = tailBits := by
            simpa [bitsTot, codeBits, tailBits] using
              (Png.shiftRight_or_shiftLeft codeBits tailBits 5
                (generatedCodeLenCodes_token_bits_lt_codeSpace hvalid))
          have hfull : bw' = bwTail' := by
            have hsplit := Png.writeBits_split bw bitsTot 5 tailLen
            simpa [bw', bwCode, bwTail', lenTot, tailLen, htailShift] using hsplit
          have hk : token.extraLen ≤ tailLen := by omega
          have htailBound :
              (Png.BitWriter.readerAt bwCode bwTail'.flush
                (Png.flush_size_writeBits_le bwCode tailBits tailLen)
                (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)).bitIndex +
                  token.extraLen ≤
                (Png.BitWriter.readerAt bwCode bwTail'.flush
                  (Png.flush_size_writeBits_le bwCode tailBits tailLen)
                  (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)).data.size * 8 := by
            simpa [bwTail', tailLen] using
              (Png.readerAt_writeBits_bound
                (bw := bwCode) (bits := tailBits) (len := tailLen)
                (k := token.extraLen) hk
                (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit))
          simpa [brCode, hfull] using htailBound) =
      (token.extraBits,
        Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot (5 + token.extraLen))
          bw'.flush
          (by
            have hk : 5 + token.extraLen ≤ lenTot := by omega
            simpa [lenTot] using
              (Png.flush_size_writeBits_prefix bw bitsTot (5 + token.extraLen) lenTot hk))
          (Png.bitPos_lt_8_writeBits bw bitsTot (5 + token.extraLen) hbit)) := by
  intro codes codeBits tailBits bitsTot lenTot bw' bwCode brCode
  let tailLen := token.extraLen + restLen
  let bwTail' := Png.BitWriter.writeBits bwCode tailBits tailLen
  have htailShift : bitsTot >>> 5 = tailBits := by
    simpa [bitsTot, codeBits, tailBits] using
      (Png.shiftRight_or_shiftLeft codeBits tailBits 5
        (generatedCodeLenCodes_token_bits_lt_codeSpace hvalid))
  have hfull : bw' = bwTail' := by
    have hsplit := Png.writeBits_split bw bitsTot 5 tailLen
    simpa [bw', bwCode, bwTail', lenTot, tailLen, htailShift] using hsplit
  have hprefixToken :
      Png.BitWriter.writeBits bw bitsTot (5 + token.extraLen) =
        Png.BitWriter.writeBits bwCode tailBits token.extraLen := by
    have hsplit := Png.writeBits_split bw bitsTot 5 token.extraLen
    simpa [bwCode, htailShift, Nat.add_assoc] using hsplit
  have hread :=
    readCodeLenTokenExtraBits_readerAt_packed
      (bw := bw) (token := token) (restBits := restBits) (restLen := restLen)
      hvalid hbit hcur
  simpa [codes, codeBits, tailBits, bitsTot, bwCode, tailLen, bwTail',
    brCode, hfull, hprefixToken] using hread

/-- Bound for reading a generated token's extra-bit field from the full packed
stream. This names the proof needed by repeat-token parser branches. -/
lemma readCodeLenTokenExtraBits_bound_readerAt_full_packed
    (bw : Png.BitWriter) {token : Png.CodeLenToken} (restBits restLen : Nat)
    (hvalid : CodeLenTokenValid token)
    (hbit : bw.bitPos < 8) :
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let codeBits := codes[token.symbol]!.1
    let tailBits := token.extraBits ||| (restBits <<< token.extraLen)
    let bitsTot := codeBits ||| (tailBits <<< 5)
    let lenTot := 5 + (token.extraLen + restLen)
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let bwCode := Png.BitWriter.writeBits bw bitsTot 5
    let brCode := Png.BitWriter.readerAt bwCode bw'.flush
      (by
        have hk : 5 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
    brCode.bitIndex + token.extraLen ≤ brCode.data.size * 8 := by
  intro codes codeBits tailBits bitsTot lenTot bw' bwCode brCode
  let tailLen := token.extraLen + restLen
  let bwTail' := Png.BitWriter.writeBits bwCode tailBits tailLen
  have htailShift : bitsTot >>> 5 = tailBits := by
    simpa [bitsTot, codeBits, tailBits] using
      (Png.shiftRight_or_shiftLeft codeBits tailBits 5
        (generatedCodeLenCodes_token_bits_lt_codeSpace hvalid))
  have hfull : bw' = bwTail' := by
    have hsplit := Png.writeBits_split bw bitsTot 5 tailLen
    simpa [bw', bwCode, bwTail', lenTot, tailLen, htailShift] using hsplit
  have hk : token.extraLen ≤ tailLen := by omega
  have htailBound :
      (Png.BitWriter.readerAt bwCode bwTail'.flush
        (Png.flush_size_writeBits_le bwCode tailBits tailLen)
        (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)).bitIndex +
          token.extraLen ≤
        (Png.BitWriter.readerAt bwCode bwTail'.flush
          (Png.flush_size_writeBits_le bwCode tailBits tailLen)
          (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)).data.size * 8 := by
    simpa [bwTail', tailLen] using
      (Png.readerAt_writeBits_bound
        (bw := bwCode) (bits := tailBits) (len := tailLen)
        (k := token.extraLen) hk
        (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit))
  simpa [brCode, hfull] using htailBound

/-- Replays one literal generated code-length token through the dynamic-table
length reader. This is the literal branch of the future token-stream induction. -/
lemma readDynamicTablesLengthsFuel_step_literal_token_generated
    (bw : Png.BitWriter) (len fuel total restBits restLen : Nat)
    (lengths : Array Nat)
    (hlen : len ≤ 15)
    (hsize : lengths.size < total)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let token := Png.CodeLenToken.literal len
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let bitsTot := codes[token.symbol]!.1 ||| (restBits <<< 5)
    let lenTot := 5 + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br5 := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 5) bw'.flush
      (by
        have hk : 5 ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
    Png.readDynamicTablesLengthsFuel (fuel + 1) total generatedCodeLenHuffman br0 lengths =
      Png.readDynamicTablesLengthsFuel fuel total generatedCodeLenHuffman br5
        (lengths.push len) := by
  intro token codes bitsTot lenTot bw' br0 br5
  have hvalid : CodeLenTokenValid token := by
    simpa [token, CodeLenTokenValid] using hlen
  have hdecode :
      generatedCodeLenHuffman.decode br0 = some (token.symbol, br5) := by
    simpa [token, bitsTot, lenTot, bw', br0, br5] using
      (generatedCodeLenHuffman_decode_token_readerAt_writeBits
        (bw := bw) (token := token) (restBits := restBits) (restLen := restLen)
        hvalid hbit hcur)
  have hstep :=
    readDynamicTablesLengthsFuel_step_literal_generated
      (fuel := fuel) (total := total) (sym := token.symbol)
      (br := br0) (br' := br5) (lengths := lengths)
      hsize hdecode (by simpa [token, Png.CodeLenToken.symbol] using hlen)
  simpa [token, Png.CodeLenToken.symbol] using hstep

/-- Replays one short zero-repeat generated code-length token through the
dynamic-table length reader. This covers DEFLATE code-length symbol `17`. -/
lemma readDynamicTablesLengthsFuel_step_repeatZeroShort_token_generated
    (bw : Png.BitWriter) (repeatCount fuel total restBits restLen : Nat)
    (lengths : Array Nat)
    (hrepeatLo : 3 ≤ repeatCount) (hrepeatHi : repeatCount ≤ 10)
    (hsize : lengths.size < total)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let token := Png.CodeLenToken.repeatZeroShort repeatCount
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let codeBits := codes[token.symbol]!.1
    let tailBits := token.extraBits ||| (restBits <<< token.extraLen)
    let bitsTot := codeBits ||| (tailBits <<< 5)
    let lenTot := 5 + (token.extraLen + restLen)
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let brToken := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot (5 + token.extraLen)) bw'.flush
      (by
        have hk : 5 + token.extraLen ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot (5 + token.extraLen) lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot (5 + token.extraLen) hbit)
    Png.readDynamicTablesLengthsFuel (fuel + 1) total generatedCodeLenHuffman br0 lengths =
      Png.readDynamicTablesLengthsFuel fuel total generatedCodeLenHuffman brToken
        (Png.pushNatRepeat lengths 0 repeatCount) := by
  intro token codes codeBits tailBits bitsTot lenTot bw' br0 brToken
  let brCode := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 5) bw'.flush
    (by
      have hk : 5 ≤ lenTot := by omega
      simpa [lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  have hvalid : CodeLenTokenValid token := by
    simpa [token, CodeLenTokenValid] using And.intro hrepeatLo hrepeatHi
  let tailLen := token.extraLen + restLen
  have hdecode :
      generatedCodeLenHuffman.decode br0 = some (token.symbol, brCode) := by
    simpa [token, bitsTot, lenTot, bw', br0, brCode, tailBits, tailLen,
      Nat.add_assoc] using
      (generatedCodeLenHuffman_decode_token_readerAt_writeBits
        (bw := bw) (token := token) (restBits := tailBits) (restLen := tailLen)
        hvalid hbit hcur)
  have hboundToken :
      brCode.bitIndex + token.extraLen ≤ brCode.data.size * 8 := by
    simpa [token, codes, codeBits, tailBits, bitsTot, lenTot, bw', brCode] using
      (readCodeLenTokenExtraBits_bound_readerAt_full_packed
        (bw := bw) (token := token) (restBits := restBits) (restLen := restLen)
        hvalid hbit)
  have hreadToken :
      brCode.readBits token.extraLen hboundToken =
        (token.extraBits, brToken) := by
    simpa [token, codes, codeBits, tailBits, bitsTot, lenTot, bw', brCode, brToken] using
      (readCodeLenTokenExtraBits_readerAt_full_packed
        (bw := bw) (token := token) (restBits := restBits) (restLen := restLen)
        hvalid hbit hcur)
  have hrepeat : 3 + token.extraBits = repeatCount := by
    simp [token, Png.CodeLenToken.extraBits]
    omega
  have hstep :=
    readDynamicTablesLengthsFuel_step_repeatZeroShort_generated
      (fuel := fuel) (total := total) (extra := token.extraBits)
      (br := br0) (brSym := brCode) (brExtra := brToken)
      (lengths := lengths) hsize
      (by simpa [token, Png.CodeLenToken.symbol] using hdecode)
      (by simpa [token, Png.CodeLenToken.extraLen] using hboundToken)
      (by simpa [token, Png.CodeLenToken.extraLen] using hreadToken)
  simpa [token, Png.CodeLenToken.symbol, hrepeat] using hstep

/-- Replays one long zero-repeat generated code-length token through the
dynamic-table length reader. This covers DEFLATE code-length symbol `18`. -/
lemma readDynamicTablesLengthsFuel_step_repeatZeroLong_token_generated
    (bw : Png.BitWriter) (repeatCount fuel total restBits restLen : Nat)
    (lengths : Array Nat)
    (hrepeatLo : 11 ≤ repeatCount) (hrepeatHi : repeatCount ≤ 138)
    (hsize : lengths.size < total)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let token := Png.CodeLenToken.repeatZeroLong repeatCount
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let codeBits := codes[token.symbol]!.1
    let tailBits := token.extraBits ||| (restBits <<< token.extraLen)
    let bitsTot := codeBits ||| (tailBits <<< 5)
    let lenTot := 5 + (token.extraLen + restLen)
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let brToken := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot (5 + token.extraLen)) bw'.flush
      (by
        have hk : 5 + token.extraLen ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot (5 + token.extraLen) lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot (5 + token.extraLen) hbit)
    Png.readDynamicTablesLengthsFuel (fuel + 1) total generatedCodeLenHuffman br0 lengths =
      Png.readDynamicTablesLengthsFuel fuel total generatedCodeLenHuffman brToken
        (Png.pushNatRepeat lengths 0 repeatCount) := by
  intro token codes codeBits tailBits bitsTot lenTot bw' br0 brToken
  let brCode := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 5) bw'.flush
    (by
      have hk : 5 ≤ lenTot := by omega
      simpa [lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  have hvalid : CodeLenTokenValid token := by
    simpa [token, CodeLenTokenValid] using And.intro hrepeatLo hrepeatHi
  let tailLen := token.extraLen + restLen
  have hdecode :
      generatedCodeLenHuffman.decode br0 = some (token.symbol, brCode) := by
    simpa [token, bitsTot, lenTot, bw', br0, brCode, tailBits, tailLen,
      Nat.add_assoc] using
      (generatedCodeLenHuffman_decode_token_readerAt_writeBits
        (bw := bw) (token := token) (restBits := tailBits) (restLen := tailLen)
        hvalid hbit hcur)
  have hboundToken :
      brCode.bitIndex + token.extraLen ≤ brCode.data.size * 8 := by
    simpa [token, codes, codeBits, tailBits, bitsTot, lenTot, bw', brCode] using
      (readCodeLenTokenExtraBits_bound_readerAt_full_packed
        (bw := bw) (token := token) (restBits := restBits) (restLen := restLen)
        hvalid hbit)
  have hreadToken :
      brCode.readBits token.extraLen hboundToken =
        (token.extraBits, brToken) := by
    simpa [token, codes, codeBits, tailBits, bitsTot, lenTot, bw', brCode, brToken] using
      (readCodeLenTokenExtraBits_readerAt_full_packed
        (bw := bw) (token := token) (restBits := restBits) (restLen := restLen)
        hvalid hbit hcur)
  have hrepeat : 11 + token.extraBits = repeatCount := by
    simp [token, Png.CodeLenToken.extraBits]
    omega
  have hstep :=
    readDynamicTablesLengthsFuel_step_repeatZeroLong_generated
      (fuel := fuel) (total := total) (extra := token.extraBits)
      (br := br0) (brSym := brCode) (brExtra := brToken)
      (lengths := lengths) hsize
      (by simpa [token, Png.CodeLenToken.symbol] using hdecode)
      (by simpa [token, Png.CodeLenToken.extraLen] using hboundToken)
      (by simpa [token, Png.CodeLenToken.extraLen] using hreadToken)
  simpa [token, Png.CodeLenToken.symbol, hrepeat] using hstep

/-- Replays one previous-length repeat generated code-length token through the
dynamic-table length reader. This covers DEFLATE code-length symbol `16`. -/
lemma readDynamicTablesLengthsFuel_step_repeatPrev_token_generated
    (bw : Png.BitWriter) (repeatCount fuel total restBits restLen : Nat)
    (lengths : Array Nat)
    (hrepeatLo : 3 ≤ repeatCount) (hrepeatHi : repeatCount ≤ 6)
    (hsize : lengths.size < total)
    (hnonempty : lengths.size ≠ 0)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let token := Png.CodeLenToken.repeatPrev repeatCount
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let codeBits := codes[token.symbol]!.1
    let tailBits := token.extraBits ||| (restBits <<< token.extraLen)
    let bitsTot := codeBits ||| (tailBits <<< 5)
    let lenTot := 5 + (token.extraLen + restLen)
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let brToken := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot (5 + token.extraLen)) bw'.flush
      (by
        have hk : 5 + token.extraLen ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot (5 + token.extraLen) lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot (5 + token.extraLen) hbit)
    Png.readDynamicTablesLengthsFuel (fuel + 1) total generatedCodeLenHuffman br0 lengths =
      Png.readDynamicTablesLengthsFuel fuel total generatedCodeLenHuffman brToken
        (Png.pushNatRepeat lengths lengths[lengths.size - 1]! repeatCount) := by
  intro token codes codeBits tailBits bitsTot lenTot bw' br0 brToken
  let brCode := Png.BitWriter.readerAt (Png.BitWriter.writeBits bw bitsTot 5) bw'.flush
    (by
      have hk : 5 ≤ lenTot := by omega
      simpa [lenTot] using
        (Png.flush_size_writeBits_prefix bw bitsTot 5 lenTot hk))
    (Png.bitPos_lt_8_writeBits bw bitsTot 5 hbit)
  have hvalid : CodeLenTokenValid token := by
    simpa [token, CodeLenTokenValid] using And.intro hrepeatLo hrepeatHi
  let tailLen := token.extraLen + restLen
  have hdecode :
      generatedCodeLenHuffman.decode br0 = some (token.symbol, brCode) := by
    simpa [token, bitsTot, lenTot, bw', br0, brCode, tailBits, tailLen,
      Nat.add_assoc] using
      (generatedCodeLenHuffman_decode_token_readerAt_writeBits
        (bw := bw) (token := token) (restBits := tailBits) (restLen := tailLen)
        hvalid hbit hcur)
  have hboundToken :
      brCode.bitIndex + token.extraLen ≤ brCode.data.size * 8 := by
    simpa [token, codes, codeBits, tailBits, bitsTot, lenTot, bw', brCode] using
      (readCodeLenTokenExtraBits_bound_readerAt_full_packed
        (bw := bw) (token := token) (restBits := restBits) (restLen := restLen)
        hvalid hbit)
  have hreadToken :
      brCode.readBits token.extraLen hboundToken =
        (token.extraBits, brToken) := by
    simpa [token, codes, codeBits, tailBits, bitsTot, lenTot, bw', brCode, brToken] using
      (readCodeLenTokenExtraBits_readerAt_full_packed
        (bw := bw) (token := token) (restBits := restBits) (restLen := restLen)
        hvalid hbit hcur)
  have hrepeat : 3 + token.extraBits = repeatCount := by
    simp [token, Png.CodeLenToken.extraBits]
    omega
  have hstep :=
    readDynamicTablesLengthsFuel_step_repeatPrev_generated
      (fuel := fuel) (total := total) (extra := token.extraBits)
      (br := br0) (brSym := brCode) (brExtra := brToken)
      (lengths := lengths) hsize hnonempty
      (by simpa [token, Png.CodeLenToken.symbol] using hdecode)
      (by simpa [token, Png.CodeLenToken.extraLen] using hboundToken)
      (by simpa [token, Png.CodeLenToken.extraLen] using hreadToken)
  simpa [token, Png.CodeLenToken.symbol, hrepeat] using hstep

/-- Replays one valid generated code-length token through the dynamic-table
length reader, producing the same array as `CodeLenToken.expand`. -/
lemma readDynamicTablesLengthsFuel_step_token_generated
    (bw : Png.BitWriter) (token : Png.CodeLenToken)
    (fuel total restBits restLen : Nat)
    (lengths lengths' : Array Nat)
    (hvalid : CodeLenTokenValid token)
    (hexpand : Png.CodeLenToken.expand lengths token = some lengths')
    (hsize : lengths.size < total)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codes := Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths
    let codeBits := codes[token.symbol]!.1
    let tailBits := token.extraBits ||| (restBits <<< token.extraLen)
    let bitsTot := codeBits ||| (tailBits <<< 5)
    let lenTot := 5 + (token.extraLen + restLen)
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br0 := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    let brToken := Png.BitWriter.readerAt
      (Png.BitWriter.writeBits bw bitsTot (5 + token.extraLen)) bw'.flush
      (by
        have hk : 5 + token.extraLen ≤ lenTot := by omega
        simpa [lenTot] using
          (Png.flush_size_writeBits_prefix bw bitsTot (5 + token.extraLen) lenTot hk))
      (Png.bitPos_lt_8_writeBits bw bitsTot (5 + token.extraLen) hbit)
    Png.readDynamicTablesLengthsFuel (fuel + 1) total generatedCodeLenHuffman br0 lengths =
      Png.readDynamicTablesLengthsFuel fuel total generatedCodeLenHuffman brToken lengths' := by
  cases token with
  | literal len =>
      intro codes codeBits tailBits bitsTot lenTot bw' br0 brToken
      have hlen : len ≤ 15 := by
        simpa [CodeLenTokenValid] using hvalid
      have hlengths' : lengths' = lengths.push len := by
        simpa [Png.CodeLenToken.expand] using hexpand.symm
      subst lengths'
      simpa [codes, codeBits, tailBits, bitsTot, lenTot, bw', br0, brToken,
        Png.CodeLenToken.symbol, Png.CodeLenToken.extraBits,
        Png.CodeLenToken.extraLen, Nat.add_assoc] using
        (readDynamicTablesLengthsFuel_step_literal_token_generated
          (bw := bw) (len := len) (fuel := fuel) (total := total)
          (restBits := restBits) (restLen := restLen) (lengths := lengths)
          hlen hsize hbit hcur)
  | repeatPrev repeatCount =>
      intro codes codeBits tailBits bitsTot lenTot bw' br0 brToken
      have hlo : 3 ≤ repeatCount := by
        simpa [CodeLenTokenValid] using hvalid.1
      have hhi : repeatCount ≤ 6 := by
        simpa [CodeLenTokenValid] using hvalid.2
      unfold Png.CodeLenToken.expand at hexpand
      by_cases hzero : lengths.size == 0
      · simp [hzero] at hexpand
      · have hnonempty : lengths.size ≠ 0 := by
          intro h
          simp [h] at hzero
        simp [hzero] at hexpand
        have hlengths' :
            lengths' =
              Png.pushNatRepeat lengths lengths[lengths.size - 1]! repeatCount := by
          exact hexpand.symm
        subst lengths'
        simpa [codes, codeBits, tailBits, bitsTot, lenTot, bw', br0, brToken,
          Png.CodeLenToken.symbol, Png.CodeLenToken.extraBits,
          Png.CodeLenToken.extraLen, Nat.add_assoc] using
          (readDynamicTablesLengthsFuel_step_repeatPrev_token_generated
            (bw := bw) (repeatCount := repeatCount) (fuel := fuel) (total := total)
            (restBits := restBits) (restLen := restLen) (lengths := lengths)
            hlo hhi hsize hnonempty hbit hcur)
  | repeatZeroShort repeatCount =>
      intro codes codeBits tailBits bitsTot lenTot bw' br0 brToken
      have hlo : 3 ≤ repeatCount := by
        simpa [CodeLenTokenValid] using hvalid.1
      have hhi : repeatCount ≤ 10 := by
        simpa [CodeLenTokenValid] using hvalid.2
      have hlengths' : lengths' = Png.pushNatRepeat lengths 0 repeatCount := by
        simpa [Png.CodeLenToken.expand] using hexpand.symm
      subst lengths'
      simpa [codes, codeBits, tailBits, bitsTot, lenTot, bw', br0, brToken,
        Png.CodeLenToken.symbol, Png.CodeLenToken.extraBits,
        Png.CodeLenToken.extraLen, Nat.add_assoc] using
        (readDynamicTablesLengthsFuel_step_repeatZeroShort_token_generated
          (bw := bw) (repeatCount := repeatCount) (fuel := fuel) (total := total)
          (restBits := restBits) (restLen := restLen) (lengths := lengths)
          hlo hhi hsize hbit hcur)
  | repeatZeroLong repeatCount =>
      intro codes codeBits tailBits bitsTot lenTot bw' br0 brToken
      have hlo : 11 ≤ repeatCount := by
        simpa [CodeLenTokenValid] using hvalid.1
      have hhi : repeatCount ≤ 138 := by
        simpa [CodeLenTokenValid] using hvalid.2
      have hlengths' : lengths' = Png.pushNatRepeat lengths 0 repeatCount := by
        simpa [Png.CodeLenToken.expand] using hexpand.symm
      subst lengths'
      simpa [codes, codeBits, tailBits, bitsTot, lenTot, bw', br0, brToken,
        Png.CodeLenToken.symbol, Png.CodeLenToken.extraBits,
        Png.CodeLenToken.extraLen, Nat.add_assoc] using
        (readDynamicTablesLengthsFuel_step_repeatZeroLong_token_generated
          (bw := bw) (repeatCount := repeatCount) (fuel := fuel) (total := total)
          (restBits := restBits) (restLen := restLen) (lengths := lengths)
          hlo hhi hsize hbit hcur)

/-- Replays a full generated code-length token stream through the dynamic-table
length reader. This lifts the one-token branch proofs to the generated header. -/
lemma readDynamicTablesLengthsFuel_codeLenTokenStream_readerAt_writeBits
    (bw : Png.BitWriter) (tokens : List Png.CodeLenToken)
    (fuelTail restBits restLen : Nat)
    (lengths lengths' : Array Nat)
    (hvalid : ∀ token ∈ tokens, CodeLenTokenValid token)
    (hexpand : codeLenTokensExpandList? tokens lengths = some lengths')
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let total := lengths.size + codeLenTokenListOutputCount tokens
    let bitsTot := codeLenTokenStreamBits tokens |||
      (restBits <<< codeLenTokenStreamLen tokens)
    let lenTot := codeLenTokenStreamLen tokens + restLen
    let bw' := Png.BitWriter.writeBits bw bitsTot lenTot
    let br := Png.BitWriter.readerAt bw bw'.flush
      (Png.flush_size_writeBits_le bw bitsTot lenTot) hbit
    Png.readDynamicTablesLengthsFuel (tokens.length + fuelTail) total
        generatedCodeLenHuffman br lengths =
      Png.readDynamicTablesLengthsFuel fuelTail total generatedCodeLenHuffman
        (Png.BitWriter.readerAt
          (Png.BitWriter.writeBits bw bitsTot (codeLenTokenStreamLen tokens))
          bw'.flush
          (by
            have hk : codeLenTokenStreamLen tokens ≤ lenTot := by omega
            simpa [lenTot] using
              (Png.flush_size_writeBits_prefix bw bitsTot
                (codeLenTokenStreamLen tokens) lenTot hk))
          (Png.bitPos_lt_8_writeBits bw bitsTot
            (codeLenTokenStreamLen tokens) hbit))
        lengths' := by
  induction tokens generalizing bw fuelTail restBits restLen lengths lengths' with
  | nil =>
      simp [codeLenTokensExpandList?, codeLenTokenStreamBits, codeLenTokenStreamLen,
        codeLenTokenListOutputCount] at hexpand ⊢
      exact hexpand ▸ rfl
  | cons token tokens ih =>
      simp [codeLenTokensExpandList?] at hexpand
      cases hexpandHead : Png.CodeLenToken.expand lengths token with
      | none =>
          simp [hexpandHead] at hexpand
      | some lengths1 =>
          simp [hexpandHead] at hexpand
          let restBits1 := codeLenTokenStreamBits tokens |||
            (restBits <<< codeLenTokenStreamLen tokens)
          let restLen1 := codeLenTokenStreamLen tokens + restLen
          let prefixBits := codeLenTokenBits token
          let streamBits := prefixBits ||| (restBits1 <<< codeLenTokenBitLen token)
          let streamLen := codeLenTokenBitLen token + restLen1
          let total := lengths.size + codeLenTokenListOutputCount (token :: tokens)
          have hheadValid : CodeLenTokenValid token := hvalid token (by simp)
          have htailValid : ∀ t ∈ tokens, CodeLenTokenValid t := by
            intro t ht
            exact hvalid t (by simp [ht])
          have hprefixBits : prefixBits < 2 ^ codeLenTokenBitLen token := by
            simpa [prefixBits] using codeLenTokenBits_lt_codeSpace hheadValid
          have hsize : lengths.size < total := by
            have hpos := codeLenTokenOutputCount_pos hheadValid
            simp [total, codeLenTokenListOutputCount]
            omega
          have hheadSize :
              lengths1.size = lengths.size + CodeLenTokenOutputCount token :=
            codeLenToken_expand_size_of_some hexpandHead
          have htotalTail :
              lengths1.size + codeLenTokenListOutputCount tokens = total := by
            simp [total, codeLenTokenListOutputCount, hheadSize, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm]
          have hbitsCons :
              codeLenTokenStreamBits (token :: tokens) |||
                  (restBits <<< codeLenTokenStreamLen (token :: tokens)) =
                streamBits := by
            simpa [streamBits, prefixBits, restBits1] using
              codeLenTokenStreamBits_cons_or_rest token tokens restBits
          have hbitsStep :
              streamBits =
                (Png.canonicalRevCodesFromLengths Png.codeLenCodeLengths)[token.symbol]!.1 |||
                  ((token.extraBits ||| (restBits1 <<< token.extraLen)) <<< 5) := by
            simpa [streamBits, prefixBits, restBits1] using
              (codeLenTokenBits_or_tail_eq_code_extra_tail token restBits1)
          have hlenCons :
              codeLenTokenStreamLen (token :: tokens) + restLen = streamLen := by
            simp [streamLen, restLen1, codeLenTokenStreamLen, codeLenTokenBitLen,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          have hlenStep :
              streamLen = 5 + (token.extraLen + restLen1) := by
            simp [streamLen, codeLenTokenBitLen, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm]
          let bwFull := Png.BitWriter.writeBits bw streamBits streamLen
          let bwPrefix := Png.BitWriter.writeBits bw streamBits (codeLenTokenBitLen token)
          let brStart := Png.BitWriter.readerAt bw bwFull.flush
            (Png.flush_size_writeBits_le bw streamBits streamLen) hbit
          let brNext := Png.BitWriter.readerAt bwPrefix bwFull.flush
            (by
              have hk : codeLenTokenBitLen token ≤ streamLen := by
                dsimp [streamLen]
                omega
              simpa [bwFull] using
                (Png.flush_size_writeBits_prefix bw streamBits
                  (codeLenTokenBitLen token) streamLen hk))
            (Png.bitPos_lt_8_writeBits bw streamBits (codeLenTokenBitLen token) hbit)
          have hstep :
              Png.readDynamicTablesLengthsFuel (tokens.length + fuelTail + 1)
                  total generatedCodeLenHuffman brStart lengths =
                Png.readDynamicTablesLengthsFuel (tokens.length + fuelTail)
                  total generatedCodeLenHuffman brNext lengths1 := by
            have hcore :=
              readDynamicTablesLengthsFuel_step_token_generated
                (bw := bw) (token := token)
                (fuel := tokens.length + fuelTail) (total := total)
                (restBits := restBits1) (restLen := restLen1)
                (lengths := lengths) (lengths' := lengths1)
                hheadValid hexpandHead hsize hbit hcur
            simpa [hbitsStep, hlenStep, bwFull, bwPrefix, brStart, brNext,
              codeLenTokenBitLen, Nat.add_assoc] using hcore
          have hprefixWriter :
              bwPrefix = Png.BitWriter.writeBits bw prefixBits (codeLenTokenBitLen token) := by
            simpa [bwPrefix, streamBits] using
              (Png.writeBits_or_shift_tail
                (bw := bw) (bits := prefixBits) (tailBits := restBits1)
                (len := codeLenTokenBitLen token) hprefixBits)
          have hfullConcat :
              Png.BitWriter.writeBits bwPrefix restBits1 restLen1 = bwFull := by
            have hconcat :
                Png.BitWriter.writeBits bw streamBits streamLen =
                  Png.BitWriter.writeBits
                    (Png.BitWriter.writeBits bw prefixBits (codeLenTokenBitLen token))
                    restBits1 restLen1 := by
              simpa [streamBits, streamLen] using
                (Png.writeBits_concat bw prefixBits restBits1
                  (codeLenTokenBitLen token) restLen1 hprefixBits)
            simpa [bwFull, hprefixWriter] using hconcat.symm
          have htail :=
            ih (bw := bwPrefix) (fuelTail := fuelTail) (restBits := restBits)
              (restLen := restLen) (lengths := lengths1) (lengths' := lengths')
              htailValid hexpand
              (Png.bitPos_lt_8_writeBits bw streamBits (codeLenTokenBitLen token) hbit)
              (Png.curClearAbove_writeBits bw streamBits (codeLenTokenBitLen token) hbit hcur)
          have htail' :
              Png.readDynamicTablesLengthsFuel (tokens.length + fuelTail)
                  total generatedCodeLenHuffman brNext lengths1 =
                Png.readDynamicTablesLengthsFuel fuelTail total generatedCodeLenHuffman
                  (Png.BitWriter.readerAt
                    (Png.BitWriter.writeBits bw streamBits
                      (codeLenTokenStreamLen (token :: tokens)))
                    bwFull.flush
                    (by
                      have hk : codeLenTokenStreamLen (token :: tokens) ≤ streamLen := by
                        dsimp [streamLen, restLen1]
                        simp [codeLenTokenStreamLen]
                      simpa [bwFull, hlenCons] using
                        (Png.flush_size_writeBits_prefix bw streamBits
                          (codeLenTokenStreamLen (token :: tokens)) streamLen hk))
                    (Png.bitPos_lt_8_writeBits bw streamBits
                      (codeLenTokenStreamLen (token :: tokens)) hbit))
                  lengths' := by
            have htailFullFlush :
                (Png.BitWriter.writeBits bwPrefix restBits1 restLen1).flush =
                  bwFull.flush := by
              rw [hfullConcat]
            have hafterWriter :
                Png.BitWriter.writeBits bwPrefix restBits1
                    (codeLenTokenStreamLen tokens) =
                  Png.BitWriter.writeBits bw streamBits
                    (codeLenTokenStreamLen (token :: tokens)) := by
              have hconcat :
                  Png.BitWriter.writeBits bw streamBits
                      (codeLenTokenBitLen token + codeLenTokenStreamLen tokens) =
                    Png.BitWriter.writeBits
                      (Png.BitWriter.writeBits bw prefixBits
                        (codeLenTokenBitLen token))
                      restBits1 (codeLenTokenStreamLen tokens) := by
                simpa [streamBits, Nat.add_assoc] using
                  (Png.writeBits_concat bw prefixBits restBits1
                    (codeLenTokenBitLen token) (codeLenTokenStreamLen tokens)
                    hprefixBits)
              simpa [hprefixWriter, codeLenTokenStreamLen, Nat.add_assoc] using
                hconcat.symm
            have hbrNextEq :
                Png.BitWriter.readerAt bwPrefix
                    ((Png.BitWriter.writeBits bwPrefix restBits1 restLen1).flush)
                    (Png.flush_size_writeBits_le bwPrefix restBits1 restLen1)
                    (Png.bitPos_lt_8_writeBits bw streamBits
                      (codeLenTokenBitLen token) hbit) =
                  brNext := by
              refine readerAt_eq_of_eqs rfl htailFullFlush _ _ _ _
            have hbrAfterEq :
                Png.BitWriter.readerAt
                    (Png.BitWriter.writeBits bwPrefix restBits1
                      (codeLenTokenStreamLen tokens))
                    ((Png.BitWriter.writeBits bwPrefix restBits1 restLen1).flush)
                    (by
                      have hk : codeLenTokenStreamLen tokens ≤ restLen1 := by
                        dsimp [restLen1]
                        omega
                      simpa using
                        (Png.flush_size_writeBits_prefix bwPrefix restBits1
                          (codeLenTokenStreamLen tokens) restLen1 hk))
                    (Png.bitPos_lt_8_writeBits bwPrefix restBits1
                      (codeLenTokenStreamLen tokens)
                      (Png.bitPos_lt_8_writeBits bw streamBits
                        (codeLenTokenBitLen token) hbit)) =
                  Png.BitWriter.readerAt
                    (Png.BitWriter.writeBits bw streamBits
                      (codeLenTokenStreamLen (token :: tokens)))
                    bwFull.flush
                    (by
                      have hk : codeLenTokenStreamLen (token :: tokens) ≤ streamLen := by
                        dsimp [streamLen, restLen1]
                        simp [codeLenTokenStreamLen]
                      simpa [bwFull, hlenCons] using
                        (Png.flush_size_writeBits_prefix bw streamBits
                          (codeLenTokenStreamLen (token :: tokens)) streamLen hk))
                    (Png.bitPos_lt_8_writeBits bw streamBits
                      (codeLenTokenStreamLen (token :: tokens)) hbit) := by
              refine readerAt_eq_of_eqs hafterWriter htailFullFlush _ _ _ _
            simpa [total, htotalTail, restBits1, restLen1, brNext, hbrNextEq,
              hbrAfterEq] using htail
          have hmain := hstep.trans htail'
          simpa [total, hbitsCons, hlenCons, bwFull, brStart, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hmain

end Lemmas

end Bitmaps
