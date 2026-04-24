import Bitmap.Lemmas.Png.DynamicBlockProofsLoopReadTables
import Bitmap.Lemmas.Png.DynamicBlockProofsPayload

namespace Bitmaps

namespace Lemmas

open Png
attribute [local simp] Png.byteArray_get_proof_irrel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
private lemma dynamicStreamReader0_readBits3 (raw : ByteArray) :
    let payloadBits := fixedLitBitsEob raw.data 0
    let hdr0 := BitWriter.empty
    let hdrHeader := BitWriter.writeBits hdr0 5 3
    let streamBits := dynamicHeaderReadBits payloadBits.1
    let streamLen := dynamicHeaderReadLen payloadBits.2
    let streamBitsFull := 5 ||| (streamBits <<< 3)
    let streamLenFull := 3 + streamLen
    let collapsedWriter := BitWriter.writeBits hdr0 streamBitsFull streamLenFull
    let hbitHeader : hdrHeader.bitPos < 8 := by
      simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide)
    let streamReader0 : BitReader := {
      data := collapsedWriter.flush
      bytePos := 0
      bitPos := 0
      hpos := by exact Nat.zero_le _
      hend := by intro _; rfl
      hbit := by decide
    }
    let streamReaderHeader := BitWriter.readerAt hdrHeader
      (BitWriter.writeBits hdrHeader streamBits streamLen).flush
      (flush_size_writeBits_le hdrHeader streamBits streamLen)
      hbitHeader
    let hread0 : streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := by
      simpa [streamReader0, BitWriter.readerAt, hdr0, BitWriter.empty] using
        (readerAt_writeBits_bound (bw := hdr0) (bits := streamBitsFull) (len := streamLenFull)
          (k := 3) (hk := by omega) (hbit := by decide))
    streamReader0.readBits 3 hread0 = (5, streamReaderHeader) := by
  let payloadBits := fixedLitBitsEob raw.data 0
  let hdr0 := BitWriter.empty
  let hdrHeader := BitWriter.writeBits hdr0 5 3
  let streamBits := dynamicHeaderReadBits payloadBits.1
  let streamLen := dynamicHeaderReadLen payloadBits.2
  let streamBitsFull := 5 ||| (streamBits <<< 3)
  let streamLenFull := 3 + streamLen
  let collapsedWriter := BitWriter.writeBits hdr0 streamBitsFull streamLenFull
  have hbitHeader : hdrHeader.bitPos < 8 := by
    simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide)
  let streamReader0 : BitReader := {
    data := collapsedWriter.flush
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide
  }
  let streamReaderHeader0 := BitWriter.readerAt hdrHeader collapsedWriter.flush
      (by
        simpa [collapsedWriter, hdrHeader, streamBitsFull, streamLenFull] using
          (flush_size_writeBits_prefix (bw := hdr0) (bits := streamBitsFull) (k := 3)
            (len := streamLenFull) (hk := by omega)))
      hbitHeader
  let streamReaderHeader := BitWriter.readerAt hdrHeader
      (BitWriter.writeBits hdrHeader streamBits streamLen).flush
      (flush_size_writeBits_le hdrHeader streamBits streamLen)
      hbitHeader
  have hstream :
      collapsedWriter = BitWriter.writeBits hdrHeader streamBits streamLen := by
    have hbits : 5 < 2 ^ 3 := by decide
    simpa [collapsedWriter, hdrHeader, streamBitsFull, streamLenFull] using
      (writeBits_concat hdr0 5 streamBits 3 streamLen hbits)
  have hstreamData :
      collapsedWriter.flush = (BitWriter.writeBits hdrHeader streamBits streamLen).flush := by
    simpa using congrArg BitWriter.flush hstream
  have hreaderEq : streamReaderHeader0 = streamReaderHeader := by
    change
      BitWriter.readerAt hdrHeader collapsedWriter.flush
        (by
          simpa [collapsedWriter, hdrHeader, streamBitsFull, streamLenFull] using
            (flush_size_writeBits_prefix (bw := hdr0) (bits := streamBitsFull) (k := 3)
              (len := streamLenFull) (hk := by omega)))
        hbitHeader =
      BitWriter.readerAt hdrHeader (BitWriter.writeBits hdrHeader streamBits streamLen).flush
        (flush_size_writeBits_le hdrHeader streamBits streamLen) hbitHeader
    exact readerAt_eq_of_eqs
      (hbw := rfl) (hdata := hstreamData)
      (hflush1 := by
        simpa [collapsedWriter, hdrHeader, streamBitsFull, streamLenFull] using
          (flush_size_writeBits_prefix (bw := hdr0) (bits := streamBitsFull) (k := 3)
            (len := streamLenFull) (hk := by omega)))
      (hflush2 := flush_size_writeBits_le hdrHeader streamBits streamLen)
      (hbit1 := hbitHeader) (hbit2 := hbitHeader)
  have hread0_at :
      (BitWriter.readerAt hdr0 collapsedWriter.flush
        (flush_size_writeBits_le hdr0 streamBitsFull streamLenFull) (by decide)).bitIndex + 3 ≤
        (BitWriter.readerAt hdr0 collapsedWriter.flush
          (flush_size_writeBits_le hdr0 streamBitsFull streamLenFull) (by decide)).data.size * 8 := by
    simpa using
      (readerAt_writeBits_bound (bw := hdr0) (bits := streamBitsFull) (len := streamLenFull)
        (k := 3) (hk := by omega) (hbit := by decide))
  have hread0 :
      streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := by
    simpa [streamReader0, BitWriter.readerAt, hdr0, BitWriter.empty] using hread0_at
  have hmod3 : streamBitsFull % 2 ^ 3 = 5 := by
    have h := mod_two_pow_or_shift (a := 5) (b := streamBits) (k := 3) (len := 3) (by decide)
    simpa [streamBitsFull] using h
  have h' :=
    (readBits_readerAt_writeBits_prefix (bw := hdr0) (bits := streamBitsFull) (len := streamLenFull)
      (k := 3) (hk := by omega) (hbit := by decide) (hcur := curClearAbove_empty)
      (hread := hread0_at))
  dsimp at h'
  have h'br0 : streamReader0.readBits 3 hread0_at = (5, streamReaderHeader0) := by
    simpa [streamReader0, streamReaderHeader0, hmod3, hdr0, BitWriter.empty] using h'
  have h'br : streamReader0.readBits 3 hread0_at = (5, streamReaderHeader) := by
    simpa [hreaderEq] using h'br0
  have hirrel : streamReader0.readBits 3 hread0 = streamReader0.readBits 3 hread0_at :=
    readBits_proof_irrel (br := streamReader0) (n := 3) hread0 hread0_at
  exact hirrel.trans h'br

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Packages the final-block dynamic branch of `zlibDecompressLoopFuel` so later proofs can plug
in any validated `DynamicTableSpec` and payload decode theorem. -/
lemma zlibDecompressLoopFuel_step_dynamic_final_of_spec
    (fuel : Nat) (br brHeader brPayload brFinal : BitReader)
    (out out' : ByteArray) (spec : DynamicTableSpec)
    (hcond : br.bitIndex + 3 ≤ br.data.size * 8)
    (hread3 : br.readBits 3 hcond = (5, brHeader))
    (hspec : readDynamicTablesSpec? brHeader = some (spec, brPayload))
    (hdecode : decodeCompressedBlock spec.litLenTable spec.distTable brPayload out =
      some (brFinal, out')) :
    zlibDecompressLoopFuel (fuel + 1) br out = some (brFinal, out') := by
  have htables :
      readDynamicTables brHeader = some (spec.litLenTable, spec.distTable, brPayload) :=
    readDynamicTablesSpec?_sound hspec
  rw [zlibDecompressLoopFuel]
  simp [hcond, hread3, htables, hdecode]

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Packages the final-block dynamic branch from a validated payload trace, so later generalized
decoder proofs can avoid unfolding `decodeCompressedBlock` directly. -/
lemma zlibDecompressLoopFuel_step_dynamic_final_of_trace
    {steps : Nat}
    (fuel : Nat) (br brHeader brPayload brFinal : BitReader)
    (out out' : ByteArray) (spec : DynamicTableSpec)
    (hcond : br.bitIndex + 3 ≤ br.data.size * 8)
    (hread3 : br.readBits 3 hcond = (5, brHeader))
    (hspec : readDynamicTablesSpec? brHeader = some (spec, brPayload))
    (htrace : DynamicPayloadTrace spec steps brPayload out brFinal out')
    (hsteps : steps ≤ brPayload.data.size * 8 + 1) :
    zlibDecompressLoopFuel (fuel + 1) br out = some (brFinal, out') := by
  have hdecode :
      decodeCompressedBlock spec.litLenTable spec.distTable brPayload out =
        some (brFinal, out') :=
    decodeCompressedBlock_of_trace htrace hsteps
  exact zlibDecompressLoopFuel_step_dynamic_final_of_spec
    (fuel := fuel) (br := br) (brHeader := brHeader)
    (brPayload := brPayload) (brFinal := brFinal)
    (out := out) (out' := out') (spec := spec)
    hcond hread3 hspec hdecode

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Specializes the generic final-block trace theorem to the public `zlibDecompressLoop` entry
point, so arbitrary validated final dynamic blocks can close the DEFLATE loop directly. -/
lemma zlibDecompressLoop_step_dynamic_final_of_trace
    {steps : Nat}
    (br brHeader brPayload brFinal : BitReader)
    (out out' : ByteArray) (spec : DynamicTableSpec)
    (hcond : br.bitIndex + 3 ≤ br.data.size * 8)
    (hread3 : br.readBits 3 hcond = (5, brHeader))
    (hspec : readDynamicTablesSpec? brHeader = some (spec, brPayload))
    (htrace : DynamicPayloadTrace spec steps brPayload out brFinal out')
    (hsteps : steps ≤ brPayload.data.size * 8 + 1) :
    zlibDecompressLoop br out = some (brFinal, out') := by
  change zlibDecompressLoopFuel (br.data.size * 8 + 1) br out = some (brFinal, out')
  exact zlibDecompressLoopFuel_step_dynamic_final_of_trace
    (fuel := br.data.size * 8) (br := br) (brHeader := brHeader)
    (brPayload := brPayload) (brFinal := brFinal)
    (out := out) (out' := out') (spec := spec)
    hcond hread3 hspec htrace hsteps

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Re-expresses the concrete dynamic-fast payload decode through a generic `DynamicTableSpec`
witness, so the concrete round-trip theorem depends on the generalized payload layer. -/
private lemma decodeCompressedBlock_dynamicStream_spec (raw : ByteArray) :
    ∃ spec,
      readDynamicTablesSpec? (dynamicStreamReaderHeader raw) =
        some (spec, dynamicStreamPayloadReaderStart raw) ∧
        spec.litLenTable = fixedLitLenHuffman ∧
        spec.distTable = fixedDistHuffman ∧
        decodeCompressedBlock spec.litLenTable spec.distTable
          (dynamicStreamPayloadReaderStart raw) ByteArray.empty =
            some
              (BitWriter.readerAt (dynamicStreamBwPrime raw) (dynamicStreamBwPrime raw).flush
                (by rfl) dynamicStreamBwPrime_bitPos_lt,
              raw) := by
  obtain ⟨spec, hspec, hlit, hdist⟩ := readDynamicTables_dynamicStream_spec raw
  let payloadBits := fixedLitBitsEob raw.data 0
  let hdr0 := BitWriter.empty
  let hdrHeader := BitWriter.writeBits hdr0 5 3
  let bwTables := BitWriter.writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen
  let streamWriter := BitWriter.writeBits bwTables payloadBits.1 payloadBits.2
  have hcur0 : hdr0.curClearAbove := curClearAbove_empty
  have hcurHeader : hdrHeader.curClearAbove := by
    simpa [hdrHeader] using curClearAbove_writeBits hdr0 5 3 (by decide) hcur0
  have hcurTables : bwTables.curClearAbove := by
    simpa [bwTables] using
      curClearAbove_writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen
        (by simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide)) hcurHeader
  have hbitHeader : hdrHeader.bitPos < 8 := by
    simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide)
  have hbitTables : bwTables.bitPos < 8 := by
    simpa [bwTables] using
      bitPos_lt_8_writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen hbitHeader
  let payloadReaderStart := BitWriter.readerAt bwTables streamWriter.flush
      (flush_size_writeBits_le bwTables payloadBits.1 payloadBits.2)
      hbitTables
  let streamReaderFinal := BitWriter.readerAt streamWriter streamWriter.flush (by rfl)
    (bitPos_lt_8_writeBits bwTables payloadBits.1 payloadBits.2 hbitTables)
  have hrawOut : byteArrayFromArray raw.data 0 ByteArray.empty = raw := by
    simpa using byteArrayFromArray_empty (data := raw.data)
  have hdecode :
      decodeCompressedBlock spec.litLenTable spec.distTable payloadReaderStart ByteArray.empty =
        some (streamReaderFinal, raw) := by
    simpa [payloadReaderStart, streamReaderFinal, payloadBits, hrawOut] using
      (decodeCompressedBlock_fixedLitBitsEob_spec
        (data := raw.data) (i := 0) (bw := bwTables) (spec := spec)
        (out := ByteArray.empty) hbitTables hcurTables hlit)
  refine ⟨spec, hspec, hlit, hdist, ?_⟩
  simpa [dynamicStreamBwPrime] using hdecode

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
private lemma decodeCompressedBlock_dynamicStream (raw : ByteArray) :
    let payloadBits := fixedLitBitsEob raw.data 0
    let hdr0 := BitWriter.empty
    let hdrHeader := BitWriter.writeBits hdr0 5 3
    let bwTables := BitWriter.writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen
    let streamWriter := BitWriter.writeBits bwTables payloadBits.1 payloadBits.2
    let hbitHeader : hdrHeader.bitPos < 8 := by
      simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide)
    let hbitTables : bwTables.bitPos < 8 := by
      simpa [bwTables] using
        bitPos_lt_8_writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen hbitHeader
    let payloadReaderStart := BitWriter.readerAt bwTables streamWriter.flush
      (flush_size_writeBits_le bwTables payloadBits.1 payloadBits.2)
      hbitTables
    let streamReaderFinal := BitWriter.readerAt streamWriter streamWriter.flush (by rfl)
      (bitPos_lt_8_writeBits bwTables payloadBits.1 payloadBits.2 hbitTables)
    decodeCompressedBlock fixedLitLenHuffman fixedDistHuffman payloadReaderStart ByteArray.empty =
      some (streamReaderFinal, raw) := by
  obtain ⟨spec, _hspec, hlit, hdist, hdecode⟩ := decodeCompressedBlock_dynamicStream_spec raw
  simpa [hlit, hdist] using hdecode

set_option maxRecDepth 400000 in
set_option maxHeartbeats 6000000 in
/-- Closes the raw DEFLATE loop proof once the dynamic header and table sections are decoded. -/
lemma zlibDecompressLoop_deflateDynamicFast_stream (raw : ByteArray) :
    let payloadBits := fixedLitBitsEob raw.data 0
    let hdr0 := BitWriter.empty
    let hdrHeader := BitWriter.writeBits hdr0 5 3
    let bwTables := BitWriter.writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen
    let streamWriter := BitWriter.writeBits bwTables payloadBits.1 payloadBits.2
    let streamBits := dynamicHeaderReadBits payloadBits.1
    let streamLen := dynamicHeaderReadLen payloadBits.2
    let streamBitsFull := 5 ||| (streamBits <<< 3)
    let streamLenFull := 3 + streamLen
    let collapsedWriter := BitWriter.writeBits hdr0 streamBitsFull streamLenFull
    let hbitHeader : hdrHeader.bitPos < 8 := by
      simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide)
    let hbitTables : bwTables.bitPos < 8 := by
      simpa [bwTables] using
        bitPos_lt_8_writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen hbitHeader
    let streamReader0 : BitReader := {
      data := collapsedWriter.flush
      bytePos := 0
      bitPos := 0
      hpos := by exact Nat.zero_le _
      hend := by intro _; rfl
      hbit := by decide
    }
    let streamReaderFinal := BitWriter.readerAt streamWriter streamWriter.flush (by rfl)
      (bitPos_lt_8_writeBits bwTables payloadBits.1 payloadBits.2 hbitTables)
    zlibDecompressLoop streamReader0 ByteArray.empty = some (streamReaderFinal, raw) := by
  classical
  let payloadBits := fixedLitBitsEob raw.data 0
  let hdr0 := BitWriter.empty
  let hdrHeader := BitWriter.writeBits hdr0 5 3
  let bwTables := BitWriter.writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen
  let streamWriter := BitWriter.writeBits bwTables payloadBits.1 payloadBits.2
  let streamBits := dynamicHeaderReadBits payloadBits.1
  let streamLen := dynamicHeaderReadLen payloadBits.2
  let streamBitsFull := 5 ||| (streamBits <<< 3)
  let streamLenFull := 3 + streamLen
  let collapsedWriter := BitWriter.writeBits hdr0 streamBitsFull streamLenFull
  let streamReader0 : BitReader := {
    data := collapsedWriter.flush
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide
  }
  have hbitHeader : hdrHeader.bitPos < 8 := by
    simpa [hdrHeader] using bitPos_lt_8_writeBits hdr0 5 3 (by decide)
  have hbitTables : bwTables.bitPos < 8 := by
    simpa [bwTables] using
      bitPos_lt_8_writeBits hdrHeader dynamicHeaderTableBits dynamicHeaderTableLen hbitHeader
  have hcur0 : hdr0.curClearAbove := curClearAbove_empty
  have hcurHeader : hdrHeader.curClearAbove := by
    simpa [hdrHeader] using curClearAbove_writeBits hdr0 5 3 (by decide) hcur0
  let streamReaderHeader := BitWriter.readerAt hdrHeader
      (BitWriter.writeBits hdrHeader streamBits streamLen).flush
      (flush_size_writeBits_le hdrHeader streamBits streamLen)
      hbitHeader
  let payloadReaderStart := BitWriter.readerAt bwTables streamWriter.flush
      (flush_size_writeBits_le bwTables payloadBits.1 payloadBits.2)
      hbitTables
  have hread3 :
      streamReader0.readBits
          3
          (by
            simpa [streamReader0, BitWriter.readerAt, hdr0, BitWriter.empty] using
              (readerAt_writeBits_bound (bw := hdr0) (bits := streamBitsFull) (len := streamLenFull)
                (k := 3) (hk := by omega) (hbit := by decide))) =
        (5, streamReaderHeader) := by
    simpa [payloadBits, hdr0, hdrHeader, streamBits, streamLen, streamBitsFull, streamLenFull,
      collapsedWriter, streamReader0, streamReaderHeader] using
      dynamicStreamReader0_readBits3 raw
  let streamReaderFinal := BitWriter.readerAt streamWriter streamWriter.flush (by rfl)
    (bitPos_lt_8_writeBits bwTables payloadBits.1 payloadBits.2 hbitTables)
  obtain ⟨spec, hspec, _hlit, _hdist, hdecode⟩ := decodeCompressedBlock_dynamicStream_spec raw
  have hcond : streamReader0.bitIndex + 3 ≤ streamReader0.data.size * 8 := by
    simpa [streamReader0, BitWriter.readerAt, hdr0, BitWriter.empty] using
      (readerAt_writeBits_bound (bw := hdr0) (bits := streamBitsFull) (len := streamLenFull)
        (k := 3) (hk := by omega) (hbit := by decide))
  change zlibDecompressLoopFuel (streamReader0.data.size * 8 + 1) streamReader0 ByteArray.empty =
      some (streamReaderFinal, raw)
  simpa [payloadBits, hdr0, hdrHeader, bwTables, streamWriter, streamBits, streamLen,
    streamBitsFull, streamLenFull, collapsedWriter, streamReader0, streamReaderHeader,
    payloadReaderStart, streamReaderFinal] using
    (zlibDecompressLoopFuel_step_dynamic_final_of_spec
      (fuel := streamReader0.data.size * 8)
      (br := streamReader0) (brHeader := streamReaderHeader)
      (brPayload := payloadReaderStart) (brFinal := streamReaderFinal)
      (out := ByteArray.empty) (out' := raw) (spec := spec)
      hcond hread3 hspec
      (by simpa [payloadBits, hdr0, hdrHeader, bwTables, streamWriter, payloadReaderStart,
          streamReaderFinal] using hdecode))

end Lemmas

end Bitmaps
