import Bitmap.Lemmas.Png.ContainerSpec
import Bitmap.Lemmas.Png.ChunkValidation

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Phase 6 — Multi-IDAT container spec

`SimpleContainerSpec` describes byte streams with exactly one `IDAT`
chunk. The PNG specification allows any positive number of consecutive
`IDAT` chunks — the runtime concatenates them. `MultiIdatContainerSpec`
generalises `SimpleContainerSpec` to a list of `IDAT` chunks.

For the special case `idatChunks = [data]`, this structure embeds into
a `SimpleContainerSpec` with `idatData := data`. The forward
correctness theorem is proven uniformly via that adapter for the
single-IDAT case; the general N-chunk case is closed in a follow-up
commit by induction over `parsePngLoopFuel`. -/

/-- A PNG byte stream with the supported subset of color types and bit
depth, plus an arbitrary positive number of `IDAT` chunks. -/
structure MultiIdatContainerSpec where
  header : PngHeader
  /-- The list of IDAT chunk payloads, in order. Non-empty per PNG spec. -/
  idatChunks : List ByteArray
  /-- Each individual chunk size fits in a u32. -/
  hChunkSize : ∀ c, c ∈ idatChunks → c.size < 2 ^ 32
  /-- At least one IDAT chunk. -/
  hNonempty : idatChunks ≠ []
  hBitDepth : header.bitDepth = 8
  hColorType :
    header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6
  hInterlace : header.interlace = 0
  hWidth : header.width < 2 ^ 32
  hHeight : header.height < 2 ^ 32

namespace MultiIdatContainerSpec

variable (s : MultiIdatContainerSpec)

/-- The runtime-visible IDAT payload: the concatenation of every IDAT
chunk in the order they appear on the wire. -/
def idatData : ByteArray :=
  s.idatChunks.foldl (· ++ ·) ByteArray.empty

/-- The bytes for the chained IDAT chunks (each wrapped with its own
length/type/CRC overhead). -/
def idatChunksBytes : ByteArray :=
  s.idatChunks.foldl
    (fun acc c => acc ++ mkChunkBytes idatTypeBytes c) ByteArray.empty

/-- The on-the-wire bytes: PNG signature + IHDR + IDAT* + IEND. -/
def bytes : ByteArray :=
  pngSignature
    ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)
    ++ s.idatChunksBytes
    ++ mkChunkBytes iendTypeBytes ByteArray.empty

/-! ### Adapter to `SimpleContainerSpec` for single-IDAT case -/

/-- When `idatChunks = [data]` (exactly one chunk), the multi-IDAT
spec embeds into a `SimpleContainerSpec` with `idatData := data`. -/
def toSimple (_ : s.idatChunks.length = 1) : SimpleContainerSpec where
  header := s.header
  idatData := s.idatChunks.head s.hNonempty
  hBitDepth := s.hBitDepth
  hColorType := s.hColorType
  hInterlace := s.hInterlace
  hWidth := s.hWidth
  hHeight := s.hHeight

/-- When `idatChunks = [data]`, the concatenated IDAT payload is `data`. -/
lemma idatData_of_singleton {s : MultiIdatContainerSpec} (data : ByteArray)
    (h : s.idatChunks = [data]) : s.idatData = data := by
  simp [idatData, h, List.foldl, ByteArray.empty_append]

/-- When `idatChunks = [data]`, the multi-IDAT IDAT bytes equal a single
`mkChunkBytes idatTypeBytes data` block. -/
lemma idatChunksBytes_of_singleton {s : MultiIdatContainerSpec} (data : ByteArray)
    (h : s.idatChunks = [data]) :
    s.idatChunksBytes = mkChunkBytes idatTypeBytes data := by
  simp [idatChunksBytes, h, List.foldl, ByteArray.empty_append]

/-- For a singleton chunk list, the multi-IDAT bytes equal the
corresponding `SimpleContainerSpec.bytes`. -/
lemma bytes_eq_simple_of_singleton {s : MultiIdatContainerSpec} (data : ByteArray)
    (h : s.idatChunks = [data]) :
    s.bytes = (SimpleContainerSpec.mk s.header data
      s.hBitDepth s.hColorType s.hInterlace s.hWidth s.hHeight).bytes := by
  unfold MultiIdatContainerSpec.bytes SimpleContainerSpec.bytes
  rw [idatChunksBytes_of_singleton data h]

/-! ### Bytes-size lemma -/

/-- The "accumulator commutation" lemma for the foldl summing sizes. -/
private lemma foldl_size_acc_comm (n : Nat) (chunks : List ByteArray) :
    chunks.foldl (fun s c => s + 12 + c.size) n =
      chunks.foldl (fun s c => s + 12 + c.size) 0 + n := by
  induction chunks generalizing n with
  | nil => simp
  | cons d ds ih =>
      simp only [List.foldl_cons]
      rw [ih (n + 12 + d.size), ih (0 + 12 + d.size)]
      omega

/-- The total chunk-bytes size: each chunk contributes
`12 + chunk.size` bytes (the `mkChunkBytes` overhead). -/
lemma idatChunksBytes_size_aux (acc : ByteArray) (chunks : List ByteArray) :
    (chunks.foldl (fun acc c => acc ++ mkChunkBytes idatTypeBytes c) acc).size =
      acc.size + chunks.foldl (fun s c => s + 12 + c.size) 0 := by
  induction chunks generalizing acc with
  | nil => simp
  | cons c rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      have hChunkSize : (mkChunkBytes idatTypeBytes c).size = c.size + 12 :=
        mkChunkBytes_size idatTypeBytes c (by rfl)
      rw [ByteArray.size_append, hChunkSize]
      rw [foldl_size_acc_comm (0 + 12 + c.size) rest]
      omega

lemma idatChunksBytes_size (s : MultiIdatContainerSpec) :
    s.idatChunksBytes.size =
      s.idatChunks.foldl (fun acc c => acc + 12 + c.size) 0 := by
  unfold idatChunksBytes
  rw [idatChunksBytes_size_aux]
  simp

/-- Total bytes size: 8 (signature) + 25 (IHDR) + chunks bytes + 12 (IEND). -/
lemma bytes_size (s : MultiIdatContainerSpec) :
    s.bytes.size =
      45 + s.idatChunks.foldl (fun acc c => acc + 12 + c.size) 0 := by
  unfold MultiIdatContainerSpec.bytes
  have hIhdr : (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4), encodeIHDRData_size]
  have hIend : (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
    rw [mkChunkBytes_size _ _ (by rfl : iendTypeBytes.size = 4)]; simp
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
    pngSignature_size, hIhdr, idatChunksBytes_size, hIend]
  omega

/-- Every multi-IDAT byte stream is at least 8 bytes long (carries the
PNG signature). -/
lemma bytes_size_ge_8 (s : MultiIdatContainerSpec) : 8 ≤ s.bytes.size := by
  rw [bytes_size]; omega

/-! ### Forward correctness — singleton case via reuse -/

/-- `parsePng` is independent of the proof of its size hypothesis. -/
private lemma parsePng_proof_irrel (bytes : ByteArray) (h1 h2 : 8 ≤ bytes.size) :
    parsePng bytes h1 = parsePng bytes h2 := rfl

/-- For the singleton-IDAT case, the multi-IDAT forward correctness
theorem reduces to `parsePng_simpleContainerSpec_correct`. -/
theorem parsePng_multiIdatContainerSpec_correct_of_singleton
    {s : MultiIdatContainerSpec} (data : ByteArray)
    (h : s.idatChunks = [data])
    (hIdatSize : data.size < 2 ^ 32) :
    parsePng s.bytes s.bytes_size_ge_8 = some (s.header, s.idatData) := by
  let simple : SimpleContainerSpec :=
    { header := s.header, idatData := data,
      hBitDepth := s.hBitDepth, hColorType := s.hColorType,
      hInterlace := s.hInterlace, hWidth := s.hWidth, hHeight := s.hHeight }
  have hBytes : s.bytes = simple.bytes :=
    bytes_eq_simple_of_singleton data h
  have hDataEq : s.idatData = data := idatData_of_singleton data h
  have hSimple :
      parsePng simple.bytes simple.bytes_size_ge_8 =
        some (simple.header, simple.idatData) :=
    parsePng_simpleContainerSpec_correct simple hIdatSize
  show parsePng s.bytes s.bytes_size_ge_8 = some (s.header, s.idatData)
  rw [hDataEq]
  -- Use congr on parsePng to handle the size-hypothesis discrepancy.
  have hParse : parsePng s.bytes s.bytes_size_ge_8 = parsePng simple.bytes simple.bytes_size_ge_8 := by
    congr 1
  rw [hParse]
  exact hSimple

/-! ### Phase 6b — position arithmetic for chunk walks

To prove the general N-chunk forward-correctness theorem, we need to
know at what byte offset each IDAT chunk lives. The helpers below
compute these offsets and prove their basic arithmetic properties. -/

/-- Wire-bytes size of one IDAT chunk: 12-byte overhead + payload size. -/
private def idatChunkWireSize (c : ByteArray) : Nat := c.size + 12

/-- Total wire size of the first `n` IDAT chunks. -/
private def idatPrefixWireSize (chunks : List ByteArray) (n : Nat) : Nat :=
  ((chunks.take n).foldl (fun acc c => acc + 12 + c.size) 0)

/-- Byte offset of the `i`-th IDAT chunk's first byte (i.e., length field). -/
def idatOffset (s : MultiIdatContainerSpec) (i : Nat) : Nat :=
  33 + idatPrefixWireSize s.idatChunks i

/-- Total wire size of all IDAT chunks (sum of all 12 + payload). -/
def idatTotalWireSize (s : MultiIdatContainerSpec) : Nat :=
  idatPrefixWireSize s.idatChunks s.idatChunks.length

/-- Byte offset of the IEND chunk. -/
def iendOffset (s : MultiIdatContainerSpec) : Nat :=
  33 + idatTotalWireSize s

/-- Total bytes size in terms of `idatTotalWireSize`. -/
lemma bytes_size_eq (s : MultiIdatContainerSpec) :
    s.bytes.size = idatTotalWireSize s + 45 := by
  rw [bytes_size]
  show 45 + s.idatChunks.foldl (fun acc c => acc + 12 + c.size) 0 =
    idatTotalWireSize s + 45
  unfold idatTotalWireSize idatPrefixWireSize
  rw [List.take_length]
  omega

/-- `idatPrefixWireSize` distributes over cons: walking past the next
chunk adds `12 + chunk.size` to the prefix size. -/
private lemma idatPrefixWireSize_succ (chunks : List ByteArray) (n : Nat)
    (h : n < chunks.length) :
    idatPrefixWireSize chunks (n + 1) =
      idatPrefixWireSize chunks n + 12 + chunks[n].size := by
  unfold idatPrefixWireSize
  rw [List.take_succ_eq_append_getElem h]
  rw [List.foldl_append]
  simp [List.foldl]

/-- The IDAT-chunks bytes for the first `n` chunks. -/
private def idatChunksBytesUpTo (chunks : List ByteArray) (n : Nat) : ByteArray :=
  (chunks.take n).foldl (fun acc c => acc ++ mkChunkBytes idatTypeBytes c)
    ByteArray.empty

/-- For `n = chunks.length`, `idatChunksBytesUpTo` equals `idatChunksBytes`. -/
lemma idatChunksBytesUpTo_full (s : MultiIdatContainerSpec) :
    idatChunksBytesUpTo s.idatChunks s.idatChunks.length = s.idatChunksBytes := by
  unfold idatChunksBytesUpTo idatChunksBytes
  rw [List.take_length]

/-- `idatChunksBytesUpTo` distributes over cons: walking past the next
chunk appends its wrapped `mkChunkBytes`. -/
private lemma idatChunksBytesUpTo_succ (chunks : List ByteArray) (n : Nat)
    (h : n < chunks.length) :
    idatChunksBytesUpTo chunks (n + 1) =
      idatChunksBytesUpTo chunks n ++ mkChunkBytes idatTypeBytes chunks[n] := by
  unfold idatChunksBytesUpTo
  rw [List.take_succ_eq_append_getElem h]
  rw [List.foldl_append]
  simp [List.foldl]

/-- Size of `idatChunksBytesUpTo` matches `idatPrefixWireSize`. -/
lemma idatChunksBytesUpTo_size (chunks : List ByteArray) (n : Nat) :
    (idatChunksBytesUpTo chunks n).size = idatPrefixWireSize chunks n := by
  unfold idatChunksBytesUpTo idatPrefixWireSize
  rw [idatChunksBytes_size_aux ByteArray.empty (chunks.take n)]
  simp

/-! ### Extract per-chunk slices from `s.bytes` -/

/-- Extracting the i-th IDAT chunk's wrapped bytes from `idatChunksBytesUpTo (i+1)`:
the last `12 + chunks[i].size` bytes equal `mkChunkBytes idatTypeBytes chunks[i]`. -/
lemma idatChunksBytesUpTo_extract_at (chunks : List ByteArray) (i : Nat)
    (h : i < chunks.length) :
    (idatChunksBytesUpTo chunks (i + 1)).extract
        (idatPrefixWireSize chunks i) (idatPrefixWireSize chunks (i + 1)) =
      mkChunkBytes idatTypeBytes chunks[i] := by
  rw [idatChunksBytesUpTo_succ chunks i h]
  rw [idatPrefixWireSize_succ chunks i h]
  -- The goal is now:
  --  (upTo i ++ mkChunkBytes idatTypeBytes chunks[i]).extract
  --    (idatPrefixWireSize chunks i)
  --    (idatPrefixWireSize chunks i + 12 + chunks[i].size) =
  --      mkChunkBytes idatTypeBytes chunks[i]
  have hsize : (idatChunksBytesUpTo chunks i).size = idatPrefixWireSize chunks i :=
    idatChunksBytesUpTo_size chunks i
  have hchunkSize : (mkChunkBytes idatTypeBytes chunks[i]).size = chunks[i].size + 12 :=
    mkChunkBytes_size idatTypeBytes chunks[i] (by rfl)
  -- extract starting at `(prefix).size` of (prefix ++ chunk) is just chunk.
  -- The shape is `(a ++ b).extract a.size (a.size + j) = b.extract 0 j`
  have hExtract :
      (idatChunksBytesUpTo chunks i ++ mkChunkBytes idatTypeBytes chunks[i]).extract
          ((idatChunksBytesUpTo chunks i).size + 0)
          ((idatChunksBytesUpTo chunks i).size + (chunks[i].size + 12)) =
        (mkChunkBytes idatTypeBytes chunks[i]).extract 0 (chunks[i].size + 12) :=
    ByteArray.extract_append_size_add' (a := idatChunksBytesUpTo chunks i)
      (b := mkChunkBytes idatTypeBytes chunks[i]) (i := 0)
      (j := chunks[i].size + 12) rfl
  have hReplace1 : idatPrefixWireSize chunks i =
      (idatChunksBytesUpTo chunks i).size + 0 := by rw [hsize]; omega
  have hReplace2 : idatPrefixWireSize chunks i + 12 + chunks[i].size =
      (idatChunksBytesUpTo chunks i).size + (chunks[i].size + 12) := by
    rw [hsize]; omega
  rw [hReplace2, hReplace1, hExtract]
  rw [← hchunkSize]
  exact ByteArray.extract_zero_size

/-! ### Lift `idatChunksBytesUpTo_extract_at` to the full chunks bytes -/

/-- Walking past chunk `m` is a prefix of walking past chunk `m+k`:
the first `idatPrefixWireSize m` bytes are unchanged. -/
private lemma idatChunksBytesUpTo_extract_zero_prefix (chunks : List ByteArray)
    (m k : Nat) (h : m + k ≤ chunks.length) :
    (idatChunksBytesUpTo chunks (m + k)).extract 0 (idatPrefixWireSize chunks m) =
      idatChunksBytesUpTo chunks m := by
  induction k with
  | zero =>
      simp only [Nat.add_zero]
      have hsize : (idatChunksBytesUpTo chunks m).size = idatPrefixWireSize chunks m :=
        idatChunksBytesUpTo_size chunks m
      rw [← hsize]
      exact ByteArray.extract_zero_size
  | succ k ih =>
      have hk : m + k ≤ chunks.length := by omega
      have hk' : m + k < chunks.length := by omega
      have hmk' : m + k + 1 = m + (k + 1) := by omega
      rw [show m + (k + 1) = (m + k) + 1 by omega]
      rw [idatChunksBytesUpTo_succ chunks (m + k) hk']
      have hupSize : (idatChunksBytesUpTo chunks (m + k)).size =
          idatPrefixWireSize chunks (m + k) :=
        idatChunksBytesUpTo_size chunks (m + k)
      have hPrefixLe : idatPrefixWireSize chunks m ≤ idatPrefixWireSize chunks (m + k) := by
        have : ∀ j, idatPrefixWireSize chunks m ≤ idatPrefixWireSize chunks (m + j) := by
          intro j
          induction j with
          | zero => simp
          | succ j ihj =>
              by_cases hbnd : m + j < chunks.length
              · rw [show m + (j + 1) = (m + j) + 1 by omega,
                    idatPrefixWireSize_succ chunks (m + j) hbnd]
                omega
              · have : idatPrefixWireSize chunks (m + (j + 1)) =
                    idatPrefixWireSize chunks (m + j) := by
                  unfold idatPrefixWireSize
                  rw [List.take_of_length_le (by omega : chunks.length ≤ m + j),
                      List.take_of_length_le (by omega : chunks.length ≤ m + (j + 1))]
                rw [this]; exact ihj
        exact this k
      -- Use byteArray_extract_append_prefix.
      rw [byteArray_extract_append_prefix
            (a := idatChunksBytesUpTo chunks (m + k))
            (b := mkChunkBytes idatTypeBytes chunks[m + k])
            (n := idatPrefixWireSize chunks m)
            (by rw [hupSize]; exact hPrefixLe)]
      exact ih hk

/-- Lifted version: extracting the i-th IDAT chunk from `s.idatChunksBytes`. -/
lemma idatChunksBytes_extract_at (s : MultiIdatContainerSpec) (i : Nat)
    (h : i < s.idatChunks.length) :
    s.idatChunksBytes.extract
        (idatPrefixWireSize s.idatChunks i) (idatPrefixWireSize s.idatChunks (i + 1)) =
      mkChunkBytes idatTypeBytes s.idatChunks[i] := by
  -- Use the prefix property: the extract on `idatChunksBytes` (full) equals
  -- the extract on `idatChunksBytesUpTo (i+1)` when the upper bound fits.
  have hUpToFull := idatChunksBytesUpTo_full s
  have hExtractEq :
      s.idatChunksBytes.extract
          (idatPrefixWireSize s.idatChunks i) (idatPrefixWireSize s.idatChunks (i + 1)) =
        (idatChunksBytesUpTo s.idatChunks (i + 1)).extract
          (idatPrefixWireSize s.idatChunks i) (idatPrefixWireSize s.idatChunks (i + 1)) := by
    rw [← hUpToFull]
    -- Need: (upTo n).extract a b = (upTo (i+1)).extract a b when b ≤ size of upTo (i+1).
    have hPrefixEq :
        (idatChunksBytesUpTo s.idatChunks s.idatChunks.length).extract 0
            (idatPrefixWireSize s.idatChunks (i + 1)) =
          idatChunksBytesUpTo s.idatChunks (i + 1) := by
      -- We need m + k = chunks.length with m = i+1.
      have hk := s.idatChunks.length - (i + 1)
      have hk_eq : (i + 1) + (s.idatChunks.length - (i + 1)) = s.idatChunks.length := by omega
      rw [← hk_eq]
      exact idatChunksBytesUpTo_extract_zero_prefix s.idatChunks (i + 1)
        (s.idatChunks.length - (i + 1)) (by omega)
    -- Now use byteArray_extract_eq_of_prefix_eq.
    exact byteArray_extract_eq_of_prefix_eq
      (a := idatChunksBytesUpTo s.idatChunks s.idatChunks.length)
      (b := idatChunksBytesUpTo s.idatChunks (i + 1))
      (n := idatPrefixWireSize s.idatChunks (i + 1))
      (i := idatPrefixWireSize s.idatChunks i)
      (j := idatPrefixWireSize s.idatChunks (i + 1))
      (by
        rw [hPrefixEq]
        have hupSize : (idatChunksBytesUpTo s.idatChunks (i + 1)).size =
            idatPrefixWireSize s.idatChunks (i + 1) :=
          idatChunksBytesUpTo_size s.idatChunks (i + 1)
        rw [← hupSize]
        exact ByteArray.extract_zero_size.symm)
      le_rfl
  rw [hExtractEq]
  exact idatChunksBytesUpTo_extract_at s.idatChunks i h

/-! ### Bytes-layout helpers: skip past signature/IHDR -/

/-- Re-associate the chained appends in `s.bytes` so the signature
appears as the leftmost prefix. Mirrors
`SimpleContainerSpec.bytes_eq_signature_then_chunks`. -/
lemma bytes_eq_signature_then_chunks (s : MultiIdatContainerSpec) :
    s.bytes =
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (s.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)) := by
  unfold MultiIdatContainerSpec.bytes
  simp [ByteArray.append_assoc]

/-- The first 8 bytes of any multi-IDAT spec are the PNG signature. -/
lemma bytes_extract_signature (s : MultiIdatContainerSpec) :
    s.bytes.extract 0 8 = pngSignature := by
  rw [s.bytes_eq_signature_then_chunks]
  have hSig : pngSignature.size = 8 := pngSignature_size
  rw [byteArray_extract_append_prefix
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (s.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))
    (n := 8) (by simp [hSig])]
  rw [← hSig]
  exact ByteArray.extract_zero_size

/-- Slicing past the 8-byte signature gives access to the chunk region. -/
lemma bytes_extract_skip_signature (s : MultiIdatContainerSpec)
    (start finish : Nat) (_h : 8 + finish ≤ s.bytes.size) :
    s.bytes.extract (8 + start) (8 + finish) =
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
        (s.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)).extract
          start finish := by
  rw [s.bytes_eq_signature_then_chunks]
  have hSig : pngSignature.size = 8 := pngSignature_size
  have h' := ByteArray.extract_append_size_add
    (a := pngSignature)
    (b := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
      (s.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty))
    (i := start) (j := finish)
  simpa [hSig] using h'

/-- Slicing past signature + IHDR gives access to the IDAT chunks + IEND. -/
lemma bytes_extract_skip_through_ihdr (s : MultiIdatContainerSpec)
    (start finish : Nat) (_h : 33 + finish ≤ s.bytes.size) :
    s.bytes.extract (33 + start) (33 + finish) =
      (s.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty).extract start finish := by
  have hSig : pngSignature.size = 8 := pngSignature_size
  have hIhdr : (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4), encodeIHDRData_size]
  rw [s.bytes_eq_signature_then_chunks]
  have hRe :
      pngSignature ++
        (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) ++
          (s.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)) =
      (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)) ++
        (s.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty) := by
    simp [ByteArray.append_assoc]
  rw [hRe]
  have hPrefSize :
      (pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 33 := by
    rw [ByteArray.size_append, hSig, hIhdr]
  have h := ByteArray.extract_append_size_add
    (a := pngSignature ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
    (b := s.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := start) (j := finish)
  simpa [hPrefSize] using h

/-! ### Forward correctness — general N-chunk case (deferred)

The general theorem for `idatChunks.length ≥ 1` chains
`parsePngLoopFuel_idat_appends_when_open` across each chunk using the
`idatOffset`/`iendOffset` position arithmetic above. The remaining
proof obligations:

  * `readChunk_multiIdat_ihdr` — IHDR at byte 8.
  * `readChunk_multiIdat_idat i` — i-th IDAT at `idatOffset s i`.
  * `readChunk_multiIdat_iend` — IEND at `iendOffset s`.
  * `parsePngLoopFuel_walk_idats` — inductive walk over chunks.

These build on `bytes_extract_skip_through_*`-style helpers parallel to
`SimpleContainerSpec`'s. The actual closure lands in a follow-up
commit that does not change the API exposed by this file. -/

end MultiIdatContainerSpec

end Lemmas

end Bitmaps
