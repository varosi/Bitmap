import Bitmap.Lemmas.Png.FixedBlockProofsCommon

namespace Bitmaps

namespace Png

/-- Public LZ77 length metadata is the fixed-Huffman match-length metadata,
packaged under the encoder-facing name used by full LZ77 payload writers. -/
lemma deflateLengthInfo_spec_internal (len : Nat) (hlo : 3 ≤ len) (hhi : len ≤ 258) :
    match deflateLengthInfo len with
    | (sym, extraBits, extraLen) =>
        ∃ _hsym : 257 ≤ sym ∧ sym ≤ 285,
          ∃ hidxBase : sym - 257 < lengthBases.size,
            ∃ hidxExtra : sym - 257 < lengthExtra.size,
              extraLen = Array.getInternal lengthExtra (sym - 257) hidxExtra ∧
              Array.getInternal lengthBases (sym - 257) hidxBase + extraBits = len ∧
              extraBits < 2 ^ extraLen := by
  simpa [deflateLengthInfo] using fixedLenMatchInfo_spec_internal len hlo hhi

/-- Successful distance-table search returns metadata that agrees with the
DEFLATE distance decoder tables. This isolates the recursive search proof. -/
lemma deflateDistanceInfoSearch_some_spec_get!
    {distance start sym extraBits extraLen : Nat}
    (hinfo :
      deflateDistanceInfoSearch distance start = some (sym, extraBits, extraLen)) :
    sym < distBases.size ∧
      extraLen = distExtra[sym]! ∧
      distBases[sym]! + extraBits = distance ∧
      extraBits < 2 ^ extraLen := by
  classical
  have hk :
      ∀ k, ∀ pos,
        deflateDistanceBases.size - pos = k →
        deflateDistanceInfoSearch distance pos = some (sym, extraBits, extraLen) →
          sym < distBases.size ∧
            extraLen = distExtra[sym]! ∧
            distBases[sym]! + extraBits = distance ∧
            extraBits < 2 ^ extraLen := by
    intro k
    induction k with
    | zero =>
        intro pos hk hinfo
        have hnot : ¬ pos < deflateDistanceBases.size := by omega
        rw [deflateDistanceInfoSearch.eq_1] at hinfo
        simp [hnot] at hinfo
    | succ k ih =>
        intro pos hk hinfo
        rw [deflateDistanceInfoSearch.eq_1] at hinfo
        by_cases hpos : pos < deflateDistanceBases.size
        · simp [hpos] at hinfo
          let base := deflateDistanceBases[pos]
          let extraLen0 := deflateDistanceExtraLens[pos]!
          let limit := base + (1 <<< extraLen0)
          by_cases hmatch : base ≤ distance ∧ distance < limit
          · rw [if_pos (by simpa [base, extraLen0, limit] using hmatch)] at hinfo
            have hdist : pos < distBases.size := by
              simpa [distBases, deflateDistanceBases] using hpos
            have hbaseEq : distBases[pos]! = base := by
              rw [getElem!_pos distBases pos hdist]
              simp [base, distBases, deflateDistanceBases]
            have hbaseLe : base ≤ distance := by
              exact hmatch.1
            have hdistLt : distance < base + 2 ^ extraLen0 := by
              simpa [base, extraLen0, limit, Nat.shiftLeft_eq, Nat.one_mul] using hmatch.2
            cases hinfo
            refine ⟨hdist, ?_, ?_, ?_⟩
            · simp [distExtra, deflateDistanceExtraLens]
            · rw [hbaseEq]
              omega
            · dsimp [base, extraLen0] at hbaseLe hdistLt
              omega
          · rw [if_neg (by simpa [base, extraLen0, limit] using hmatch)] at hinfo
            have hk' : deflateDistanceBases.size - (pos + 1) = k := by omega
            exact ih (pos + 1) hk' hinfo
        · simp [hpos] at hinfo
  exact hk (deflateDistanceBases.size - start) start rfl hinfo

/-- If `deflateDistanceInfo?` returns metadata, the encoded distance symbol and
extra bits reconstruct the original distance in the decoder tables. -/
lemma deflateDistanceInfo?_some_spec_get!
    {distance sym extraBits extraLen : Nat}
    (hinfo : deflateDistanceInfo? distance = some (sym, extraBits, extraLen)) :
    sym < distBases.size ∧
      extraLen = distExtra[sym]! ∧
      distBases[sym]! + extraBits = distance ∧
      extraBits < 2 ^ extraLen := by
  unfold deflateDistanceInfo? at hinfo
  by_cases hvalid : 1 ≤ distance && distance ≤ deflateMaxDistance
  · exact deflateDistanceInfoSearch_some_spec_get!
      (distance := distance) (start := 0) (sym := sym)
      (extraBits := extraBits) (extraLen := extraLen)
      (by simpa [hvalid] using hinfo)
  · simp [hvalid] at hinfo

/-- Successful distance metadata can be used with the decoder's internal
array proofs, avoiding repeated `get!` coercion in payload proofs. -/
lemma deflateDistanceInfo?_some_spec_internal
    {distance sym extraBits extraLen : Nat}
    (hinfo : deflateDistanceInfo? distance = some (sym, extraBits, extraLen)) :
    ∃ hdist : sym < distBases.size,
      ∃ hdistExtra : sym < distExtra.size,
        extraLen = Array.getInternal distExtra sym hdistExtra ∧
        Array.getInternal distBases sym hdist + extraBits = distance ∧
        extraBits < 2 ^ extraLen := by
  rcases deflateDistanceInfo?_some_spec_get! hinfo with
    ⟨hdist, hextraGet, hbaseGet, hbitsLt⟩
  have hDistExtraSize : distExtra.size = 30 := by decide
  have hDistBasesSize : distBases.size = 30 := by decide
  have hdistExtra : sym < distExtra.size := by
    simpa [hDistExtraSize, hDistBasesSize] using hdist
  have hbaseInternal : Array.getInternal distBases sym hdist = distBases[sym]! :=
    array_getInternal_eq_get! distBases sym hdist
  have hextraInternal : Array.getInternal distExtra sym hdistExtra = distExtra[sym]! :=
    array_getInternal_eq_get! distExtra sym hdistExtra
  refine ⟨hdist, hdistExtra, ?_, ?_, hbitsLt⟩
  · calc
      extraLen = distExtra[sym]! := hextraGet
      _ = Array.getInternal distExtra sym hdistExtra := hextraInternal.symm
  · calc
      Array.getInternal distBases sym hdist + extraBits =
          distBases[sym]! + extraBits := by rw [hbaseInternal]
      _ = distance := hbaseGet

/-- The distance extra bits written after a DEFLATE distance symbol decode
back to the advertised distance and leave the reader after those bits. -/
lemma decodeDistance_readerAt_writeBits_prefix
    (bw : BitWriter) (sym extraBits extraLen restBits restLen distance : Nat)
    (hdist : sym < distBases.size)
    (hdistExtra : sym < distExtra.size)
    (hextra : extraLen = Array.getInternal distExtra sym hdistExtra)
    (hbase : Array.getInternal distBases sym hdist + extraBits = distance)
    (hbitsLt : extraBits < 2 ^ extraLen)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsTot := extraBits ||| (restBits <<< extraLen)
    let lenTot := extraLen + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    decodeDistance sym br hdist
      (by
        have hread :=
          readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := extraLen)
            (hk := by omega) (hbit := hbit)
        have hDistExtraSize : distExtra.size = 30 := by decide
        have hDistBasesSize : distBases.size = 30 := by decide
        have hdistExtraCanon : sym < distExtra.size := by
          simpa [hDistExtraSize, hDistBasesSize] using hdist
        have hcanon :
            distExtra[sym]'hdistExtraCanon = extraLen := by
          calc
            distExtra[sym]'hdistExtraCanon =
                Array.getInternal distExtra sym hdistExtraCanon := rfl
            _ = Array.getInternal distExtra sym hdistExtra := by
                  congr
            _ = extraLen := by simpa using hextra.symm
        simpa [br, bw', lenTot, hcanon] using hread) =
      (distance,
        BitWriter.readerAt (BitWriter.writeBits bw bitsTot extraLen) bw'.flush
          (by
            have hk : extraLen ≤ lenTot := by omega
            simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot extraLen lenTot hk))
          (bitPos_lt_8_writeBits bw bitsTot extraLen hbit)) := by
  let bitsTot := extraBits ||| (restBits <<< extraLen)
  let lenTot := extraLen + restLen
  let bw' := BitWriter.writeBits bw bitsTot lenTot
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
  let brExtra := BitWriter.readerAt (BitWriter.writeBits bw bitsTot extraLen) bw'.flush
    (by
      have hk : extraLen ≤ lenTot := by omega
      simpa [bw', lenTot] using (flush_size_writeBits_prefix bw bitsTot extraLen lenTot hk))
    (bitPos_lt_8_writeBits bw bitsTot extraLen hbit)
  have hreadExtra : br.bitIndex + extraLen ≤ br.data.size * 8 := by
    simpa [br, bw', lenTot] using
      (readerAt_writeBits_bound (bw := bw) (bits := bitsTot) (len := lenTot) (k := extraLen)
        (hk := by omega) (hbit := hbit))
  have hbitsRead :
      br.readBits extraLen hreadExtra = (bitsTot % 2 ^ extraLen, brExtra) := by
    simpa [br, bw', brExtra, lenTot] using
      (readBits_readerAt_writeBits_prefix (bw := bw) (bits := bitsTot) (len := lenTot)
        (k := extraLen) (hk := by omega) (hbit := hbit) (hcur := hcur))
  have hmodExtra : bitsTot % 2 ^ extraLen = extraBits := by
    have h :=
      mod_two_pow_or_shift (a := extraBits) (b := restBits) (k := extraLen) (len := extraLen)
        (by exact le_rfl)
    have hmod : extraBits % 2 ^ extraLen = extraBits := Nat.mod_eq_of_lt hbitsLt
    simpa [bitsTot, hmod] using h
  have hbitsRead' :
      br.readBits extraLen hreadExtra = (extraBits, brExtra) := by
    calc
      br.readBits extraLen hreadExtra = (bitsTot % 2 ^ extraLen, brExtra) := hbitsRead
      _ = (extraBits, brExtra) := by simp [hmodExtra]
  have hDistExtraSize : distExtra.size = 30 := by decide
  have hDistBasesSize : distBases.size = 30 := by decide
  have hdistExtraCanon : sym < distExtra.size := by
    simpa [hDistExtraSize, hDistBasesSize] using hdist
  have hcanonExtra :
      distExtra[sym]'hdistExtraCanon = extraLen := by
    calc
      distExtra[sym]'hdistExtraCanon =
          Array.getInternal distExtra sym hdistExtraCanon := rfl
      _ = Array.getInternal distExtra sym hdistExtra := by
            congr
      _ = extraLen := by simpa using hextra.symm
  have hcanonBasePlus :
      distBases[sym]'hdist + extraBits = distance := by
    simpa using hbase
  by_cases hextra0 : extraLen = 0
  · have hbrEq : brExtra = br := by
      apply BitReader.ext
      all_goals
        simp [brExtra, br, bw', bitsTot, lenTot, hextra0, writeBits_zero]
    have hbaseCanon0 :
        distBases[sym]'hdist = distance := by
      have hbits0 : extraBits = 0 := by
        have : extraBits < 1 := by simpa [hextra0] using hbitsLt
        omega
      omega
    have hbitsArg :
        br.bitIndex + distExtra[sym]'hdistExtraCanon ≤ br.data.size * 8 := by
      simpa [br, bw', lenTot, hcanonExtra, hextra0] using hreadExtra
    have hdecode :
        decodeDistance sym br hdist hbitsArg = (distance, br) := by
      unfold decodeDistance
      have hcanonExtra0 : distExtra[sym]'hdistExtraCanon = 0 := by
        simpa [hcanonExtra] using hextra0
      simp [hcanonExtra0, hbaseCanon0]
    simpa [bitsTot, lenTot, bw', br, brExtra, hbrEq] using hdecode
  · have hbitsArg :
      br.bitIndex + distExtra[sym]'hdistExtraCanon ≤ br.data.size * 8 := by
      simpa [br, bw', lenTot, hcanonExtra] using hreadExtra
    have hdecode :
        decodeDistance sym br hdist hbitsArg = (distance, brExtra) := by
      unfold decodeDistance
      have hcanonExtraNe0 : ¬ distExtra[sym]'hdistExtraCanon = 0 := by
        simpa [hcanonExtra] using hextra0
      have hreadEq :
          br.readBits (distExtra[sym]'hdistExtraCanon) hbitsArg =
            br.readBits extraLen hreadExtra := by
        have hbitsArg' : br.bitIndex + extraLen ≤ br.data.size * 8 := by
          simpa [hcanonExtra] using hbitsArg
        calc
          br.readBits (distExtra[sym]'hdistExtraCanon) hbitsArg =
              br.readBits extraLen hbitsArg' := by
                simp [hcanonExtra]
          _ = br.readBits extraLen hreadExtra := by
                exact readBits_proof_irrel (br := br) (n := extraLen)
                  (h1 := hbitsArg') (h2 := hreadExtra)
      simp [hcanonExtraNe0]
      rw [hreadEq, hbitsRead']
      simp [hcanonBasePlus]
    simpa [bitsTot, lenTot, bw', br, brExtra] using hdecode

/-- A successful LZ77 copy could not have taken the runtime failure branch, so
the copied distance is nonzero and within the current output size. -/
lemma lz77CopyDistanceFast_some_distance_valid
    {out out' : ByteArray} {distance len : Nat}
    (hcopy : lz77CopyDistanceFast out distance len = some out') :
    1 ≤ distance ∧ distance ≤ out.size := by
  unfold lz77CopyDistanceFast at hcopy
  by_cases hbad : distance = 0 || distance > out.size
  · simp [hbad] at hcopy
  · have hgood := hbad
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hgood
    exact ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero hgood.1), Nat.le_of_not_gt hgood.2⟩

/-- A successful LZ77 match-token expansion exposes all encoder-side validity
facts needed by fixed and dynamic payload trace builders. -/
lemma lz77TokenExpand?_match_some_spec
    {out out' : ByteArray} {len distance : Nat}
    (h : lz77TokenExpand? out (.match len distance) = some out') :
    deflateMinMatchLen ≤ len ∧ len ≤ deflateMaxMatchLen ∧
      1 ≤ distance ∧ distance ≤ deflateMaxDistance ∧
      distance ≤ out.size ∧
      (∃ info, deflateDistanceInfo? distance = some info) ∧
      lz77CopyDistanceFast out distance len = some out' := by
  unfold lz77TokenExpand? at h
  by_cases hvalid :
      deflateMinMatchLen ≤ len && len ≤ deflateMaxMatchLen &&
        1 ≤ distance && distance ≤ deflateMaxDistance &&
        (deflateDistanceInfo? distance).isSome
  · have hcopy : lz77CopyDistanceFast out distance len = some out' := by
      simpa [hvalid] using h
    cases hinfo : deflateDistanceInfo? distance with
    | none =>
        simp [hinfo] at hvalid
    | some info =>
        have hprops := hvalid
        simp only [hinfo, Bool.and_eq_true, decide_eq_true_eq] at hprops
        rcases hprops with ⟨⟨⟨⟨hlenLo, hlenHi⟩, hdistLo⟩, hdistHi⟩, _hinfoSome⟩
        have hcopyValid := lz77CopyDistanceFast_some_distance_valid hcopy
        exact ⟨hlenLo, hlenHi, hdistLo, hdistHi, hcopyValid.2, ⟨info, rfl⟩, hcopy⟩
  · simp [hvalid] at h

/-- Successful match expansion uses the same copy routine as the decoder's
`copyDistance`, because the decoder has been switched to the LZ77 copy path. -/
lemma lz77TokenExpand?_match_some_copyDistance
    {out out' : ByteArray} {len distance : Nat}
    (h : lz77TokenExpand? out (.match len distance) = some out') :
    copyDistance out distance len = some out' := by
  rcases lz77TokenExpand?_match_some_spec (out := out) (out' := out')
      (len := len) (distance := distance) h with
    ⟨_, _, _, _, _, _, hcopy⟩
  simpa [copyDistance] using hcopy

end Png

end Bitmaps
