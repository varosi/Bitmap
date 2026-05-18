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
a `SimpleContainerSpec` with `idatData := data`. The singleton case is
proven uniformly via that adapter; the general N-chunk case
(`parsePng_multiIdatContainerSpec_correct`) is closed by induction over
`parsePngLoopFuel`, with `parsePngSimple_eq_none_of_multi` ruling out
the fast-path return for length ≥ 2. -/

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
  hBitDepth : header.bitDepth = 1 ∨ header.bitDepth = 8 ∨ header.bitDepth = 16
  hColorType :
    header.colorType = 0 ∨ header.colorType = 2 ∨
      header.colorType = 4 ∨ header.colorType = 6
  hCtBdSupported :
    pngColorTypeBitDepthSupported header.colorType header.bitDepth = true
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
  hCtBdSupported := s.hCtBdSupported
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
      s.hBitDepth s.hColorType s.hCtBdSupported s.hInterlace
      s.hWidth s.hHeight).bytes := by
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
      hCtBdSupported := s.hCtBdSupported,
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
def idatPrefixWireSize (chunks : List ByteArray) (n : Nat) : Nat :=
  ((chunks.take n).foldl (fun acc c => acc + 12 + c.size) 0)

/-- Byte offset of the `i`-th IDAT chunk's first byte (i.e., length field). -/
def idatOffset (s : MultiIdatContainerSpec) (i : Nat) : Nat :=
  33 + idatPrefixWireSize s.idatChunks i

/-- Total wire size of all IDAT chunks (sum of all 12 + payload). -/
def idatTotalWireSize (s : MultiIdatContainerSpec) : Nat :=
  MultiIdatContainerSpec.idatPrefixWireSize s.idatChunks s.idatChunks.length

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
lemma idatPrefixWireSize_succ (chunks : List ByteArray) (n : Nat)
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

/-! ### Project per-chunk extracts to `s.bytes` -/

/-- `idatPrefixWireSize` walking past one more chunk doesn't decrease the prefix size. -/
lemma idatPrefixWireSize_succ_ge (chunks : List ByteArray) (m : Nat) :
    idatPrefixWireSize chunks m ≤ idatPrefixWireSize chunks (m + 1) := by
  by_cases hbnd : m < chunks.length
  · rw [idatPrefixWireSize_succ chunks m hbnd]; omega
  · have : idatPrefixWireSize chunks (m + 1) = idatPrefixWireSize chunks m := by
      unfold idatPrefixWireSize
      rw [List.take_of_length_le (by omega : chunks.length ≤ m),
          List.take_of_length_le (by omega : chunks.length ≤ m + 1)]
    omega

/-- `idatPrefixWireSize` is monotone in the prefix length. -/
lemma idatPrefixWireSize_mono (chunks : List ByteArray) (m n : Nat)
    (h : m ≤ n) :
    idatPrefixWireSize chunks m ≤ idatPrefixWireSize chunks n := by
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.mp h
      rw [this]
  | succ k ihk =>
      by_cases hmk : m ≤ k
      · exact Nat.le_trans (ihk hmk) (idatPrefixWireSize_succ_ge chunks k)
      · have : m = k + 1 := by omega
        rw [this]

/-- The i-th wrapped IDAT chunk in `s.bytes` lives at the right offset. -/
lemma bytes_extract_idat_at (s : MultiIdatContainerSpec) (i : Nat)
    (h : i < s.idatChunks.length) :
    s.bytes.extract (idatOffset s i) (idatOffset s (i + 1)) =
      mkChunkBytes idatTypeBytes s.idatChunks[i] := by
  unfold idatOffset
  -- Step 1: skip past signature + IHDR.
  have hSizeBound : 33 + idatPrefixWireSize s.idatChunks (i + 1) ≤ s.bytes.size := by
    rw [s.bytes_size_eq]
    unfold idatTotalWireSize
    have hmono := idatPrefixWireSize_mono s.idatChunks (i + 1) s.idatChunks.length (by omega)
    omega
  rw [s.bytes_extract_skip_through_ihdr (idatPrefixWireSize s.idatChunks i)
        (idatPrefixWireSize s.idatChunks (i + 1)) hSizeBound]
  -- Step 2: the extract is entirely within `idatChunksBytes` (not crossing into IEND).
  have hWithinIdat : idatPrefixWireSize s.idatChunks (i + 1) ≤ s.idatChunksBytes.size := by
    rw [show s.idatChunksBytes.size = idatPrefixWireSize s.idatChunks s.idatChunks.length from ?_]
    · exact idatPrefixWireSize_mono s.idatChunks (i + 1) s.idatChunks.length (by omega)
    · rw [← idatChunksBytesUpTo_size, idatChunksBytesUpTo_full]
  rw [byteArray_extract_append_left
        (a := s.idatChunksBytes)
        (b := mkChunkBytes iendTypeBytes ByteArray.empty)
        (i := idatPrefixWireSize s.idatChunks i)
        (j := idatPrefixWireSize s.idatChunks (i + 1))
        (Nat.le_trans (idatPrefixWireSize_mono s.idatChunks i (i + 1) (by omega))
          hWithinIdat)
        hWithinIdat]
  -- Step 3: apply the per-chunk extract on `idatChunksBytes`.
  exact idatChunksBytes_extract_at s i h

/-! ### Per-chunk `readChunk` lemma -/

/-- Helper: a sub-extract of `s.bytes` within the i-th wrapped IDAT chunk
range equals the corresponding sub-extract of `mkChunkBytes idatTypeBytes chunks[i]`. -/
private lemma bytes_subextract_idat_at (s : MultiIdatContainerSpec) (i : Nat)
    (h : i < s.idatChunks.length) (a b : Nat) (hab : a ≤ b)
    (hb : b ≤ 12 + s.idatChunks[i].size) :
    s.bytes.extract (idatOffset s i + a) (idatOffset s i + b) =
      (mkChunkBytes idatTypeBytes s.idatChunks[i]).extract a b := by
  -- Use ByteArray.extract_extract to relate the sub-extract to the full chunk extract.
  have hChunkSize : (mkChunkBytes idatTypeBytes s.idatChunks[i]).size =
      s.idatChunks[i].size + 12 :=
    mkChunkBytes_size idatTypeBytes s.idatChunks[i] (by rfl)
  have hWidth : idatOffset s (i + 1) = idatOffset s i + (12 + s.idatChunks[i].size) := by
    unfold idatOffset
    rw [idatPrefixWireSize_succ s.idatChunks i h]
    omega
  have hFull := bytes_extract_idat_at s i h
  -- (s.bytes.extract (idatOffset s i) (idatOffset s (i+1))).extract a b
  --   = mkChunkBytes idatTypeBytes chunks[i].extract a b
  have hExtract :
      (s.bytes.extract (idatOffset s i) (idatOffset s (i + 1))).extract a b =
        (mkChunkBytes idatTypeBytes s.idatChunks[i]).extract a b := by
    rw [hFull]
  -- LHS via extract_extract:
  -- (s.bytes.extract i j).extract k l = s.bytes.extract (i+k) (min j (i+l))
  have hMin : min (idatOffset s i + b) (idatOffset s (i + 1)) = idatOffset s i + b := by
    rw [hWidth]; omega
  have hCalc :
      (s.bytes.extract (idatOffset s i) (idatOffset s (i + 1))).extract a b =
        s.bytes.extract (idatOffset s i + a) (idatOffset s i + b) := by
    have h := ByteArray.extract_extract (a := s.bytes)
      (i := idatOffset s i) (j := idatOffset s (i + 1))
      (k := a) (l := b)
    rw [hMin] at h
    exact h
  rw [← hCalc]; exact hExtract

/-! ### Generic `readChunk` at `mkChunkBytes` offset

`readChunk_at_mkChunkBytes` is a reusable lemma over any
`mkChunkBytes`-shaped region in a byte stream: given a bytes-level
extract that the region's bytes equal a wrapped chunk, `readChunk`
returns the corresponding type / data / next-position triple. -/

-- `mkChunkBytes` length field is the first 4 bytes.
lemma mkChunkBytes_extract_len (typBytes data : ByteArray) :
    (mkChunkBytes typBytes data).extract 0 4 = u32be data.size := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  simpa [mkChunkBytes_def, hlen] using
    (ByteArray.extract_append_eq_left
      (a := u32be data.size)
      (b := typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat)
      (i := (u32be data.size).size) rfl)

-- `mkChunkBytes` type bytes are at positions [4, 8).
private lemma mkChunkBytes_extract_type (typBytes data : ByteArray)
    (htyp : typBytes.size = 4) :
    (mkChunkBytes typBytes data).extract 4 8 = typBytes := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  have h1 :
      (mkChunkBytes typBytes data).extract 4 8 =
        (typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat).extract 0 4 := by
    simpa [mkChunkBytes_def, hlen, ByteArray.append_assoc] using
      (ByteArray.extract_append_size_add
        (a := u32be data.size)
        (b := typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat)
        (i := 0) (j := 4))
  have h2' :
      (typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat).extract 0
          typBytes.size = typBytes := by
    simpa [ByteArray.append_assoc] using
      (ByteArray.extract_append_eq_left
        (a := typBytes)
        (b := data ++ u32be (crc32Chunk typBytes data).toNat)
        (i := typBytes.size) rfl)
  have h2 :
      (typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat).extract 0 4 =
        typBytes := by
    simpa [htyp] using h2'
  rw [h1, h2]

-- `mkChunkBytes` data bytes are at positions [8, 8 + data.size).
private lemma mkChunkBytes_extract_data (typBytes data : ByteArray)
    (htyp : typBytes.size = 4) :
    (mkChunkBytes typBytes data).extract 8 (8 + data.size) = data := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  have hprefix : (u32be data.size ++ typBytes).size = 8 := by
    rw [ByteArray.size_append, hlen, htyp]
  have h1 :
      (mkChunkBytes typBytes data).extract 8 (8 + data.size) =
        (data ++ u32be (crc32Chunk typBytes data).toNat).extract 0 data.size := by
    simpa [mkChunkBytes_def, hprefix, ByteArray.append_assoc] using
      (ByteArray.extract_append_size_add
        (a := u32be data.size ++ typBytes)
        (b := data ++ u32be (crc32Chunk typBytes data).toNat)
        (i := 0) (j := data.size))
  have h2 :
      (data ++ u32be (crc32Chunk typBytes data).toNat).extract 0 data.size = data := by
    simpa using
      (ByteArray.extract_append_eq_left
        (a := data)
        (b := u32be (crc32Chunk typBytes data).toNat)
        (i := data.size) rfl)
  rw [h1, h2]

-- `mkChunkBytes` CRC is at positions [8 + data.size, 12 + data.size).
private lemma mkChunkBytes_extract_crc (typBytes data : ByteArray)
    (htyp : typBytes.size = 4) :
    (mkChunkBytes typBytes data).extract (8 + data.size) (12 + data.size) =
      u32be (crc32Chunk typBytes data).toNat := by
  have hlen : (u32be data.size).size = 4 := u32be_size _
  have hprefix : (u32be data.size ++ typBytes ++ data).size = 8 + data.size := by
    rw [ByteArray.size_append, ByteArray.size_append, hlen, htyp]
  -- Rewrite mkChunkBytes into its left-associated form first.
  rw [mkChunkBytes_def]
  -- Now LHS is `(u32be size ++ typBytes ++ data ++ u32be CRC).extract ...`
  have h1 :
      (u32be data.size ++ typBytes ++ data ++ u32be (crc32Chunk typBytes data).toNat).extract
          (8 + data.size) (12 + data.size) =
        (u32be (crc32Chunk typBytes data).toNat).extract 0 4 := by
    have h := ByteArray.extract_append_size_add
      (a := u32be data.size ++ typBytes ++ data)
      (b := u32be (crc32Chunk typBytes data).toNat)
      (i := 0) (j := 4)
    rw [hprefix] at h
    rw [show (12 + data.size : Nat) = 8 + data.size + 4 by omega]
    simpa using h
  rw [h1]
  have hcrcLen : (u32be (crc32Chunk typBytes data).toNat).size = 4 := u32be_size _
  rw [show (4 : Nat) = (u32be (crc32Chunk typBytes data).toNat).size from hcrcLen.symm]
  exact ByteArray.extract_zero_size

set_option maxHeartbeats 800000 in
/-- The generic `readChunk` reduction over any `mkChunkBytes`-shaped
region in a byte stream. Given that `bytes[pos..pos+12+data.size]`
equals the wrapped chunk, `readChunk` returns the matching triple.

This is the reusable kernel that both single-IDAT and multi-IDAT
readChunk lemmas can build on, avoiding per-position simp-evaluation
of the readChunk case-analytic definition. -/
lemma readChunk_at_mkChunkBytes (bytes : ByteArray) (pos : Nat)
    (typBytes data : ByteArray)
    (hTypSize : typBytes.size = 4)
    (hDataSize : data.size < 2 ^ 32)
    (hWrap : bytes.extract pos (pos + 12 + data.size) = mkChunkBytes typBytes data)
    (hSize : pos + 12 + data.size ≤ bytes.size)
    (hLen : pos + 3 < bytes.size) :
    readChunk bytes pos hLen =
      some (typBytes, data, pos + 8 + data.size + 4) := by
  -- Derive each sub-extract from the wrapped-chunk extract via
  -- `ByteArray.extract_extract`, then apply the `mkChunkBytes_extract_*` lemmas.
  have hWrapSize : (mkChunkBytes typBytes data).size = data.size + 12 :=
    mkChunkBytes_size typBytes data hTypSize
  have hChunkRange : pos + 12 + data.size = pos + (12 + data.size) := by omega
  -- Sub-extract helper: for `0 ≤ a ≤ b ≤ 12 + data.size`, the sub-extract on
  -- bytes equals the sub-extract on the wrapped chunk.
  have hSubExtract : ∀ (a b : Nat), a ≤ b → b ≤ 12 + data.size →
      bytes.extract (pos + a) (pos + b) =
        (mkChunkBytes typBytes data).extract a b := by
    intro a b _hab hb
    have hMin : min (pos + b) (pos + 12 + data.size) = pos + b := by
      omega
    have hExt :
        (bytes.extract pos (pos + 12 + data.size)).extract a b =
          bytes.extract (pos + a) (pos + b) := by
      have h := ByteArray.extract_extract (a := bytes)
        (i := pos) (j := pos + 12 + data.size) (k := a) (l := b)
      rw [hMin] at h
      exact h
    rw [← hExt, hWrap]
  -- Length field.
  have hExtractLen :
      bytes.extract pos (pos + 4) = u32be data.size := by
    have h := hSubExtract 0 4 (by omega) (by omega)
    simp at h
    rw [h]
    exact mkChunkBytes_extract_len typBytes data
  have hLenRead : readU32BE bytes pos hLen = data.size :=
    readU32BE_of_extract_eq bytes pos data.size hLen hExtractLen hDataSize
  -- Type bytes.
  have hExtractType :
      bytes.extract (pos + 4) (pos + 8) = typBytes := by
    have h := hSubExtract 4 8 (by omega) (by omega)
    rw [h]
    exact mkChunkBytes_extract_type typBytes data hTypSize
  -- Data bytes.
  have hExtractData :
      bytes.extract (pos + 8) (pos + 8 + data.size) = data := by
    have h := hSubExtract 8 (8 + data.size) (by omega) (by omega)
    rw [show pos + 8 + data.size = pos + (8 + data.size) by omega]
    rw [h]
    exact mkChunkBytes_extract_data typBytes data hTypSize
  -- CRC bytes.
  have hExtractCrc :
      bytes.extract (pos + 8 + data.size) (pos + 12 + data.size) =
        u32be (crc32Chunk typBytes data).toNat := by
    have h := hSubExtract (8 + data.size) (12 + data.size) (by omega) (by omega)
    rw [show pos + 8 + data.size = pos + (8 + data.size) by omega,
        show pos + 12 + data.size = pos + (12 + data.size) by omega]
    rw [h]
    exact mkChunkBytes_extract_crc typBytes data hTypSize
  -- CRC value.
  have hExtractCrc' :
      bytes.extract (pos + 8 + data.size) (pos + 8 + data.size + 4) =
        u32be (crc32Chunk typBytes data).toNat := by
    rw [show pos + 8 + data.size + 4 = pos + 12 + data.size by omega]
    exact hExtractCrc
  have hCrcRead :
      readU32BE bytes (pos + 8 + data.size) (by omega) =
        (crc32Chunk typBytes data).toNat :=
    readU32BE_of_extract_eq bytes (pos + 8 + data.size) _
      (by omega) hExtractCrc' (UInt32.toNat_lt _)
  -- CRC-end bound.
  have hCrcEnd : pos + 8 + data.size + 4 ≤ bytes.size := by omega
  -- Combine via readChunk's definition.
  unfold readChunk
  simp [hLenRead, hCrcEnd, hExtractType, hExtractData, hCrcRead]

/-! ### Per-chunk readChunk lemma (uses the generic helper) -/

set_option maxHeartbeats 800000 in
/-- readChunk at the i-th IDAT chunk's offset reads idatTypeBytes, the
chunk data, and the position right after the chunks CRC. -/
lemma readChunk_multiIdat_idat (s : MultiIdatContainerSpec) (i : Nat)
    (h : i < s.idatChunks.length)
    (hLen : idatOffset s i + 3 < s.bytes.size) :
    readChunk s.bytes (idatOffset s i) hLen =
      some (idatTypeBytes, s.idatChunks[i],
        idatOffset s i + 8 + s.idatChunks[i].size + 4) := by
  have hChunkSize := s.hChunkSize s.idatChunks[i] (List.getElem_mem h)
  have hChunkRangeBound : idatOffset s i + 12 + s.idatChunks[i].size ≤ s.bytes.size := by
    rw [s.bytes_size_eq]
    unfold idatOffset idatTotalWireSize
    have hStep : idatPrefixWireSize s.idatChunks i + 12 + s.idatChunks[i].size =
        idatPrefixWireSize s.idatChunks (i + 1) := by
      rw [idatPrefixWireSize_succ s.idatChunks i h]
    have hmono := idatPrefixWireSize_mono s.idatChunks (i + 1) s.idatChunks.length (by omega)
    omega
  -- The wrapped chunk's bytes live at the right offset.
  have hWrap :
      s.bytes.extract (idatOffset s i) (idatOffset s i + 12 + s.idatChunks[i].size) =
        mkChunkBytes idatTypeBytes s.idatChunks[i] := by
    have h' := s.bytes_extract_idat_at i h
    have hWidth : idatOffset s (i + 1) = idatOffset s i + 12 + s.idatChunks[i].size := by
      unfold idatOffset
      rw [idatPrefixWireSize_succ s.idatChunks i h]; omega
    rw [← hWidth]; exact h'
  exact readChunk_at_mkChunkBytes s.bytes (idatOffset s i)
    idatTypeBytes s.idatChunks[i] (by rfl) hChunkSize hWrap hChunkRangeBound hLen

/-! ### IHDR and IEND readChunk lemmas (via the kernel) -/

/-- The IHDR chunk's bytes live at byte offset 8 in `s.bytes`. -/
lemma bytes_extract_ihdr (s : MultiIdatContainerSpec) :
    s.bytes.extract 8 (8 + 12 + (encodeIHDRData s.header).size) =
      mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header) := by
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  -- Substitute (encodeIHDRData s.header).size to its numeric value 13 first.
  rw [hIhdrSize]
  have h := s.bytes_extract_skip_signature 0 (12 + 13)
    (by rw [s.bytes_size_eq]; unfold idatTotalWireSize; omega)
  rw [show (8 : Nat) + 0 = 8 from rfl] at h
  rw [h]
  -- The result is (IHDR ++ (chunks ++ IEND)).extract 0 25 = IHDR (since IHDR has size 25).
  have hIhdrChunkSize :
      (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size = 25 := by
    rw [mkChunkBytes_size _ _ (by rfl : ihdrTypeBytes.size = 4), hIhdrSize]
  rw [byteArray_extract_append_prefix
        (a := mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header))
        (b := s.idatChunksBytes ++ mkChunkBytes iendTypeBytes ByteArray.empty)
        (n := 25)
        (by rw [hIhdrChunkSize])]
  rw [show (25 : Nat) = (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).size from
    hIhdrChunkSize.symm]
  exact ByteArray.extract_zero_size

set_option maxHeartbeats 800000 in
/-- readChunk at byte 8 reads `(ihdrTypeBytes, encodeIHDRData s.header, 33)`. -/
lemma readChunk_multiIdat_ihdr (s : MultiIdatContainerSpec)
    (hLen : 8 + 3 < s.bytes.size) :
    readChunk s.bytes 8 hLen =
      some (ihdrTypeBytes, encodeIHDRData s.header, 33) := by
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hSize : 8 + 12 + (encodeIHDRData s.header).size ≤ s.bytes.size := by
    rw [s.bytes_size_eq, hIhdrSize]
    unfold idatTotalWireSize
    omega
  have hIhdrFits : (encodeIHDRData s.header).size < 2 ^ 32 := by
    rw [hIhdrSize]; decide
  have h := readChunk_at_mkChunkBytes s.bytes 8 ihdrTypeBytes (encodeIHDRData s.header)
    (by rfl) hIhdrFits (s.bytes_extract_ihdr) hSize hLen
  rw [show 8 + 8 + (encodeIHDRData s.header).size + 4 = 33 from by rw [hIhdrSize]] at h
  exact h

/-- The IEND chunk's bytes live at byte offset `iendOffset s`. -/
lemma bytes_extract_iend (s : MultiIdatContainerSpec) :
    s.bytes.extract (iendOffset s) (iendOffset s + 12 + ByteArray.empty.size) =
      mkChunkBytes iendTypeBytes ByteArray.empty := by
  have hEmptySize : (ByteArray.empty : ByteArray).size = 0 := rfl
  -- Use bytes_extract_skip_through_ihdr with offsets relative to byte 33.
  -- iendOffset = 33 + idatTotalWireSize. We want extract from iendOffset to iendOffset+12.
  -- Skipping past 33 gives us bytes in (idatChunksBytes ++ iendChunk).
  unfold iendOffset
  rw [show (33 + idatTotalWireSize s : Nat) = 33 + idatTotalWireSize s from rfl]
  rw [hEmptySize, Nat.add_zero]
  have hSize : 33 + (idatTotalWireSize s + 12) ≤ s.bytes.size := by
    rw [s.bytes_size_eq]; omega
  have h := s.bytes_extract_skip_through_ihdr (idatTotalWireSize s)
    (idatTotalWireSize s + 12) hSize
  rw [show (33 + (idatTotalWireSize s + 12) : Nat) = 33 + idatTotalWireSize s + 12 by omega] at h
  rw [h]
  -- (idatChunksBytes ++ iendChunk).extract idatTotalWireSize (idatTotalWireSize + 12) = iendChunk
  have hIdatChunksSize : s.idatChunksBytes.size = idatTotalWireSize s := by
    rw [idatChunksBytes_size]
    unfold idatTotalWireSize idatPrefixWireSize
    rw [List.take_length]
  have h' := ByteArray.extract_append_size_add (a := s.idatChunksBytes)
    (b := mkChunkBytes iendTypeBytes ByteArray.empty)
    (i := 0) (j := 12)
  rw [hIdatChunksSize] at h'
  rw [show (s.idatTotalWireSize + 0 : Nat) = s.idatTotalWireSize from by omega] at h'
  rw [h']
  -- Result is iendChunk.extract 0 12 = iendChunk.
  have hIendSize : (mkChunkBytes iendTypeBytes ByteArray.empty).size = 12 := by
    rw [mkChunkBytes_size _ _ (by rfl : iendTypeBytes.size = 4)]
    simp
  rw [show (12 : Nat) = (mkChunkBytes iendTypeBytes ByteArray.empty).size from hIendSize.symm]
  exact ByteArray.extract_zero_size

set_option maxHeartbeats 800000 in
/-- readChunk at `iendOffset s` reads `(iendTypeBytes, empty, bytes.size)`. -/
lemma readChunk_multiIdat_iend (s : MultiIdatContainerSpec)
    (hLen : iendOffset s + 3 < s.bytes.size) :
    readChunk s.bytes (iendOffset s) hLen =
      some (iendTypeBytes, ByteArray.empty, s.bytes.size) := by
  have hSize : iendOffset s + 12 + ByteArray.empty.size ≤ s.bytes.size := by
    rw [s.bytes_size_eq]
    unfold iendOffset
    simp
    omega
  have hEmptyFits : (ByteArray.empty : ByteArray).size < 2 ^ 32 := by decide
  have h := readChunk_at_mkChunkBytes s.bytes (iendOffset s) iendTypeBytes ByteArray.empty
    (by rfl) hEmptyFits (s.bytes_extract_iend) hSize hLen
  rw [show iendOffset s + 8 + ByteArray.empty.size + 4 = s.bytes.size from ?_] at h
  · exact h
  · rw [s.bytes_size_eq]
    unfold iendOffset
    simp
    omega

/-! ### parsePngLoopFuel step lemmas -/

set_option maxHeartbeats 800000 in
/-- `parsePngLoopFuel` step lemma for the IEND closing branch:
given an IEND chunk that completes the byte stream, with state
having `seenIDAT = true`, the loop returns the accumulated state. -/
lemma parsePngLoopFuel_iend_success_step (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngParseState)
    (hdr : PngHeader)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (iendTypeBytes, ByteArray.empty, bytes.size))
    (hheader : state.header = some hdr)
    (hSeenIDAT : state.seenIDAT = true) :
    parsePngLoopFuel (fuel + 1) bytes pos state = some (hdr, state.idat) := by
  conv => lhs; unfold parsePngLoopFuel
  have hNotIHDR : (iendTypeBytes == ihdrTypeBytes) = false := by decide
  have hNotPLTE : (iendTypeBytes == plteTypeBytes) = false := by decide
  have hNotIDAT : (iendTypeBytes == idatTypeBytes) = false := by decide
  have hIsIEND : (iendTypeBytes == iendTypeBytes) = true := by decide
  have hEmptySize : (ByteArray.empty.size != 0) = false := by decide
  have hPosEq : (bytes.size != bytes.size) = false := by simp
  simp [hpos, hLen, hread, hheader, hNotIHDR, hNotPLTE, hNotIDAT, hIsIEND,
    hEmptySize, hSeenIDAT, hPosEq]

/-- After processing the first `i` IDAT chunks of a multi-IDAT spec,
the loop state has `idat = concat of first i chunks` and `seenIDAT = true`
(for i ≥ 1). The inductive step uses
`parsePngLoopFuel_idat_appends_when_open`. -/
private def stateAfterIdats (s : MultiIdatContainerSpec) (i : Nat) : PngParseState :=
  { header := some s.header
    idat := s.idatChunks.take i |>.foldl (· ++ ·) ByteArray.empty
    seenPLTE := false
    seenIDAT := 0 < i
    closedIDAT := false
    metadata := PngMetadata.empty }

/-- The accumulated `idat` after all `n` chunks equals `s.idatData`. -/
private lemma stateAfterIdats_idat_full (s : MultiIdatContainerSpec) :
    (stateAfterIdats s s.idatChunks.length).idat = s.idatData := by
  unfold stateAfterIdats idatData
  rw [List.take_length]

/-- The `idat` field accumulates one more chunk at each step. -/
private lemma stateAfterIdats_idat_succ (s : MultiIdatContainerSpec) (i : Nat)
    (h : i < s.idatChunks.length) :
    (stateAfterIdats s (i + 1)).idat =
      (stateAfterIdats s i).idat ++ s.idatChunks[i] := by
  unfold stateAfterIdats
  show (s.idatChunks.take (i + 1)).foldl (· ++ ·) ByteArray.empty =
    (s.idatChunks.take i).foldl (· ++ ·) ByteArray.empty ++ s.idatChunks[i]
  rw [List.take_succ_eq_append_getElem h]
  rw [List.foldl_append]
  simp [List.foldl]

set_option maxHeartbeats 1200000 in
/-- `parsePngLoopFuel` walks through one IDAT chunk: given the state after
processing the first `i` chunks, processing chunk `i` produces the state
after `i+1` chunks at the next position. -/
lemma parsePngLoopFuel_walk_idat_step (s : MultiIdatContainerSpec) (i : Nat)
    (h : i < s.idatChunks.length)
    (fuel : Nat)
    (hRest : parsePngLoopFuel fuel s.bytes (idatOffset s (i + 1))
              (stateAfterIdats s (i + 1)) = some (s.header, s.idatData)) :
    parsePngLoopFuel (fuel + 1) s.bytes (idatOffset s i)
        (stateAfterIdats s i) = some (s.header, s.idatData) := by
  -- Compute readChunk at idatOffset s i.
  have hChunkRangeBound : idatOffset s i + 12 + s.idatChunks[i].size ≤ s.bytes.size := by
    rw [s.bytes_size_eq]
    unfold idatOffset idatTotalWireSize
    have hStep : idatPrefixWireSize s.idatChunks i + 12 + s.idatChunks[i].size =
        idatPrefixWireSize s.idatChunks (i + 1) := by
      rw [idatPrefixWireSize_succ s.idatChunks i h]
    have hmono := idatPrefixWireSize_mono s.idatChunks (i + 1) s.idatChunks.length
      (by omega)
    omega
  have hLen : idatOffset s i + 3 < s.bytes.size := by omega
  have hPos : idatOffset s i + 8 ≤ s.bytes.size := by omega
  have hReadIdat := s.readChunk_multiIdat_idat i h hLen
  have hNextOffsetEq : idatOffset s i + 8 + s.idatChunks[i].size + 4 = idatOffset s (i + 1) := by
    unfold idatOffset
    rw [idatPrefixWireSize_succ s.idatChunks i h]
    omega
  rw [hNextOffsetEq] at hReadIdat
  -- Color type != 3 (from hColorType).
  have hPalette :
      ((stateAfterIdats s i).header.elim 0 PngHeader.colorType == 3 &&
       !(stateAfterIdats s i).seenPLTE) = false := by
    unfold stateAfterIdats
    simp
    rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide
  -- Apply parsePngLoopFuel_idat_appends_when_open.
  have hStep := parsePngLoopFuel_idat_appends_when_open fuel s.bytes (idatOffset s i)
    (stateAfterIdats s i) s.header idatTypeBytes s.idatChunks[i] (idatOffset s (i + 1))
    hPos hLen hReadIdat
    (by unfold stateAfterIdats; rfl)
    (by decide) (by decide) (by decide)
    (by unfold stateAfterIdats; rfl)
    (by
      unfold stateAfterIdats
      simp
      rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide)
  rw [hStep]
  -- Now state after step matches stateAfterIdats s (i+1).
  have hIdatEq : (stateAfterIdats s i).idat ++ s.idatChunks[i] =
      (stateAfterIdats s (i + 1)).idat := by
    rw [stateAfterIdats_idat_succ s i h]
  have hStateEq :
      ({ header := some s.header
         idat := (stateAfterIdats s i).idat ++ s.idatChunks[i]
         seenPLTE := (stateAfterIdats s i).seenPLTE
         seenIDAT := true
         closedIDAT := false
         metadata := (stateAfterIdats s i).metadata : PngParseState }) =
      stateAfterIdats s (i + 1) := by
    rw [hIdatEq]
    unfold stateAfterIdats
    have hSucc : (0 < i + 1) = True := by simp
    rfl
  rw [hStateEq]
  exact hRest

/-! ### Inductive walk and main theorem -/

set_option maxHeartbeats 1200000 in
/-- Inductive walk: starting from the state after `i` IDAT chunks at the
i-th chunk's offset, with sufficient fuel, the loop walks all remaining
chunks plus IEND and returns the final state. -/
lemma parsePngLoopFuel_walk_idats_aux (s : MultiIdatContainerSpec) (i : Nat)
    (hi : i ≤ s.idatChunks.length)
    (fuel : Nat) (hFuel : s.idatChunks.length - i + 1 ≤ fuel) :
    parsePngLoopFuel fuel s.bytes (idatOffset s i)
      (stateAfterIdats s i) = some (s.header, s.idatData) := by
  -- Induction on `n - i`.
  induction h : s.idatChunks.length - i generalizing i fuel with
  | zero =>
      -- i = n, state-after-n has full idat. Read IEND.
      have hin : i = s.idatChunks.length := by omega
      cases fuel with
      | zero =>
          rw [hin] at hFuel
          simp at hFuel
      | succ fuel' =>
          have hOffsetEq : idatOffset s i = iendOffset s := by
            unfold idatOffset iendOffset idatTotalWireSize
            rw [hin]
          rw [hOffsetEq]
          have hLen : iendOffset s + 3 < s.bytes.size := by
            rw [s.bytes_size_eq]; unfold iendOffset; omega
          have hPos : iendOffset s + 8 ≤ s.bytes.size := by
            rw [s.bytes_size_eq]; unfold iendOffset; omega
          have hReadIend := s.readChunk_multiIdat_iend hLen
          have hSeenIDAT : (stateAfterIdats s i).seenIDAT = true := by
            unfold stateAfterIdats
            simp
            rw [hin]
            cases hChunks : s.idatChunks with
            | nil => exact absurd hChunks s.hNonempty
            | cons _ _ => simp
          have hHeader : (stateAfterIdats s i).header = some s.header := rfl
          have hIdatEq : (stateAfterIdats s i).idat = s.idatData := by
            rw [hin]
            exact stateAfterIdats_idat_full s
          rw [← hIdatEq]
          exact parsePngLoopFuel_iend_success_step fuel' s.bytes (iendOffset s)
            (stateAfterIdats s i) s.header hPos hLen hReadIend hHeader hSeenIDAT
  | succ k ih =>
      -- i < n, walk one chunk then recurse.
      have hilt : i < s.idatChunks.length := by omega
      cases fuel with
      | zero =>
          have : s.idatChunks.length - i + 1 ≤ 0 := hFuel
          omega
      | succ fuel' =>
          have hi' : i + 1 ≤ s.idatChunks.length := by omega
          have hk' : s.idatChunks.length - (i + 1) = k := by omega
          have hFuel' : s.idatChunks.length - (i + 1) + 1 ≤ fuel' := by
            have hkfuel : s.idatChunks.length - i + 1 ≤ fuel' + 1 := hFuel
            omega
          have hRest := ih (i := i + 1) hi' fuel' hFuel' hk'
          exact parsePngLoopFuel_walk_idat_step s i hilt fuel' hRest

set_option maxHeartbeats 1200000 in
/-- The opening step: from the empty state at byte 8, after one fuel unit
the loop transitions to the state after 0 IDATs (just IHDR read). -/
lemma parsePngLoopFuel_walk_ihdr_step (s : MultiIdatContainerSpec) (fuel : Nat)
    (hFuel : s.idatChunks.length + 1 ≤ fuel)
    (hHeader : (encodeIHDRData s.header).size < 2 ^ 32 := by decide) :
    parsePngLoopFuel (fuel + 1) s.bytes 8
      { header := none, idat := ByteArray.empty,
        seenPLTE := false, seenIDAT := false, closedIDAT := false,
        metadata := PngMetadata.empty } =
      some (s.header, s.idatData) := by
  have hPos : (8 : Nat) + 8 ≤ s.bytes.size := by
    rw [s.bytes_size_eq]; unfold idatTotalWireSize
    have hmono := idatPrefixWireSize_mono s.idatChunks 0 s.idatChunks.length (by omega)
    omega
  have hLen : (8 : Nat) + 3 < s.bytes.size := by omega
  have hReadIhdr := s.readChunk_multiIdat_ihdr hLen
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hCT256 : s.header.colorType < 256 := by
    rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide
  have hBDlt : s.header.bitDepth < 256 := by
    rcases s.hBitDepth with h | h | h <;> rw [h] <;> decide
  have hParseHdr := parseIHDRData_encodeIHDRData_lt256 s.header
    s.hWidth s.hHeight hBDlt s.hInterlace hCT256
  -- Unfold parsePngLoopFuel.
  conv => lhs; unfold parsePngLoopFuel
  -- The state has header = none, so we take the IHDR branch.
  have hReadU32Len : readU32BE s.bytes 8 hLen = 13 := by
    have hExtractLen :
        s.bytes.extract 8 (8 + 4) = u32be 13 := by
      have h := s.bytes_extract_ihdr
      -- The first 4 bytes of the IHDR chunk are u32be 13.
      have hChunkLen := mkChunkBytes_extract_len ihdrTypeBytes (encodeIHDRData s.header)
      rw [hIhdrSize] at hChunkLen
      -- (s.bytes.extract 8 (8 + 12 + 13)).extract 0 4 = u32be 13
      have hsub : (s.bytes.extract 8 (8 + 12 + (encodeIHDRData s.header).size)).extract 0 4 =
          (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).extract 0 4 := by
        rw [h]
      rw [hChunkLen] at hsub
      -- Also (s.bytes.extract 8 X).extract 0 4 = s.bytes.extract 8 (min X (8+4))
      have hExt := ByteArray.extract_extract (a := s.bytes) (i := 8)
        (j := 8 + 12 + (encodeIHDRData s.header).size) (k := 0) (l := 4)
      have hMin : min (8 + 4) (8 + 12 + (encodeIHDRData s.header).size) = 8 + 4 := by
        rw [hIhdrSize]; omega
      rw [hMin] at hExt
      rw [← hExt]
      exact hsub
    exact readU32BE_of_extract_eq s.bytes 8 13 hLen hExtractLen (by decide)
  -- Now compute the rest.
  simp [hPos, hLen, hReadIhdr, hReadU32Len, hParseHdr]
  -- After parsing IHDR, the state has header := some s.header, etc.
  -- This matches stateAfterIdats s 0 except for `metadata := PngMetadata.empty`.
  -- The recursive call is parsePngLoopFuel fuel s.bytes 33 newState.
  have hOffsetEq : (33 : Nat) = idatOffset s 0 := by
    unfold idatOffset idatPrefixWireSize
    simp
  have hStateEq :
      ({ header := some s.header, idat := ByteArray.empty,
         seenPLTE := false, seenIDAT := false, closedIDAT := false,
         metadata := PngMetadata.empty } : PngParseState) =
      stateAfterIdats s 0 := by
    unfold stateAfterIdats
    simp [List.foldl]
  rw [hOffsetEq, hStateEq]
  refine ⟨by decide, ?_⟩
  exact parsePngLoopFuel_walk_idats_aux s 0 (by omega) fuel
    (by omega)

/-! ### Metadata-aware loop walk (Phase 6c)

The metadata-aware `parsePngLoopFuelWithMetadata` shares the same IHDR /
IDAT / IEND control flow as `parsePngLoopFuel`; the only structural
difference is that it threads a `PngMetadataParseState` (carrying the
`PngMetadata` payload) through the recursion. For a byte stream
matching `MultiIdatContainerSpec` (no ancillary chunks), the metadata
field remains `PngMetadata.empty` throughout, and the proof structure
mirrors Phase 6b's basic-loop walk verbatim. -/

set_option maxHeartbeats 800000 in
/-- Metadata-aware analogue of `parsePngLoopFuel_iend_success_step`: an
IEND chunk closing the byte stream returns the accumulated state's
header, IDAT, and metadata payload. -/
lemma parsePngLoopFuelWithMetadata_iend_success_step (fuel : Nat)
    (bytes : ByteArray) (pos : Nat) (state : PngMetadataParseState)
    (hdr : PngHeader)
    (hpos : pos + 8 ≤ bytes.size) (hLen : pos + 3 < bytes.size)
    (hread : readChunk bytes pos hLen = some (iendTypeBytes, ByteArray.empty, bytes.size))
    (hheader : state.header = some hdr)
    (hSeenIDAT : state.seenIDAT = true) :
    parsePngLoopFuelWithMetadata (fuel + 1) bytes pos state =
      some { header := hdr, idat := state.idat, metadata := state.metadata } := by
  conv => lhs; unfold parsePngLoopFuelWithMetadata
  have hNotIHDR : (iendTypeBytes == ihdrTypeBytes) = false := by decide
  have hNotPLTE : (iendTypeBytes == plteTypeBytes) = false := by decide
  have hNotIDAT : (iendTypeBytes == idatTypeBytes) = false := by decide
  have hIsIEND : (iendTypeBytes == iendTypeBytes) = true := by decide
  have hEmptySize : (ByteArray.empty.size != 0) = false := by decide
  have hPosEq : (bytes.size != bytes.size) = false := by simp
  simp [hpos, hLen, hread, hheader, hNotIHDR, hNotPLTE, hNotIDAT, hIsIEND,
    hEmptySize, hSeenIDAT, hPosEq]

/-- Metadata-aware state-after-`i`-IDATs: parallel to `stateAfterIdats`
but carrying the empty `PngMetadata`. -/
private def stateAfterIdatsM (s : MultiIdatContainerSpec) (i : Nat) :
    PngMetadataParseState :=
  { header := some s.header
    idat := s.idatChunks.take i |>.foldl (· ++ ·) ByteArray.empty
    seenPLTE := false
    seenIDAT := 0 < i
    closedIDAT := false
    metadata := PngMetadata.empty }

/-- After all `n` chunks, `stateAfterIdatsM.idat = s.idatData`. -/
private lemma stateAfterIdatsM_idat_full (s : MultiIdatContainerSpec) :
    (stateAfterIdatsM s s.idatChunks.length).idat = s.idatData := by
  unfold stateAfterIdatsM idatData
  rw [List.take_length]

/-- `stateAfterIdatsM.idat` accumulates one more chunk at each step. -/
private lemma stateAfterIdatsM_idat_succ (s : MultiIdatContainerSpec) (i : Nat)
    (h : i < s.idatChunks.length) :
    (stateAfterIdatsM s (i + 1)).idat =
      (stateAfterIdatsM s i).idat ++ s.idatChunks[i] := by
  unfold stateAfterIdatsM
  show (s.idatChunks.take (i + 1)).foldl (· ++ ·) ByteArray.empty =
    (s.idatChunks.take i).foldl (· ++ ·) ByteArray.empty ++ s.idatChunks[i]
  rw [List.take_succ_eq_append_getElem h]
  rw [List.foldl_append]
  simp [List.foldl]

set_option maxHeartbeats 1200000 in
/-- Metadata-aware analogue of `parsePngLoopFuel_walk_idat_step`. -/
lemma parsePngLoopFuelWithMetadata_walk_idat_step (s : MultiIdatContainerSpec) (i : Nat)
    (h : i < s.idatChunks.length)
    (fuel : Nat)
    (hRest : parsePngLoopFuelWithMetadata fuel s.bytes (idatOffset s (i + 1))
              (stateAfterIdatsM s (i + 1)) =
              some { header := s.header, idat := s.idatData,
                     metadata := PngMetadata.empty }) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes (idatOffset s i)
        (stateAfterIdatsM s i) =
      some { header := s.header, idat := s.idatData,
             metadata := PngMetadata.empty } := by
  have hChunkRangeBound : idatOffset s i + 12 + s.idatChunks[i].size ≤ s.bytes.size := by
    rw [s.bytes_size_eq]
    unfold idatOffset idatTotalWireSize
    have hStep : idatPrefixWireSize s.idatChunks i + 12 + s.idatChunks[i].size =
        idatPrefixWireSize s.idatChunks (i + 1) := by
      rw [idatPrefixWireSize_succ s.idatChunks i h]
    have hmono := idatPrefixWireSize_mono s.idatChunks (i + 1) s.idatChunks.length
      (by omega)
    omega
  have hLen : idatOffset s i + 3 < s.bytes.size := by omega
  have hPos : idatOffset s i + 8 ≤ s.bytes.size := by omega
  have hReadIdat := s.readChunk_multiIdat_idat i h hLen
  have hNextOffsetEq :
      idatOffset s i + 8 + s.idatChunks[i].size + 4 = idatOffset s (i + 1) := by
    unfold idatOffset
    rw [idatPrefixWireSize_succ s.idatChunks i h]
    omega
  rw [hNextOffsetEq] at hReadIdat
  have hStep := parsePngLoopFuelWithMetadata_idat_appends_when_open fuel s.bytes
    (idatOffset s i) (stateAfterIdatsM s i) s.header idatTypeBytes
    s.idatChunks[i] (idatOffset s (i + 1))
    hPos hLen hReadIdat
    (by unfold stateAfterIdatsM; rfl)
    (by decide) (by decide) (by decide)
    (by unfold stateAfterIdatsM; rfl)
    (by
      unfold stateAfterIdatsM
      simp
      rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide)
  rw [hStep]
  have hIdatEq : (stateAfterIdatsM s i).idat ++ s.idatChunks[i] =
      (stateAfterIdatsM s (i + 1)).idat := by
    rw [stateAfterIdatsM_idat_succ s i h]
  have hStateEq :
      ({ header := some s.header
         idat := (stateAfterIdatsM s i).idat ++ s.idatChunks[i]
         seenPLTE := (stateAfterIdatsM s i).seenPLTE
         seenIDAT := true
         closedIDAT := false
         metadata := (stateAfterIdatsM s i).metadata : PngMetadataParseState }) =
      stateAfterIdatsM s (i + 1) := by
    rw [hIdatEq]
    unfold stateAfterIdatsM
    rfl
  rw [hStateEq]
  exact hRest

set_option maxHeartbeats 1200000 in
/-- Metadata-aware inductive walk over all remaining chunks plus IEND. -/
lemma parsePngLoopFuelWithMetadata_walk_idats_aux (s : MultiIdatContainerSpec) (i : Nat)
    (hi : i ≤ s.idatChunks.length)
    (fuel : Nat) (hFuel : s.idatChunks.length - i + 1 ≤ fuel) :
    parsePngLoopFuelWithMetadata fuel s.bytes (idatOffset s i)
      (stateAfterIdatsM s i) =
      some { header := s.header, idat := s.idatData,
             metadata := PngMetadata.empty } := by
  induction h : s.idatChunks.length - i generalizing i fuel with
  | zero =>
      have hin : i = s.idatChunks.length := by omega
      cases fuel with
      | zero =>
          rw [hin] at hFuel
          simp at hFuel
      | succ fuel' =>
          have hOffsetEq : idatOffset s i = iendOffset s := by
            unfold idatOffset iendOffset idatTotalWireSize
            rw [hin]
          rw [hOffsetEq]
          have hLen : iendOffset s + 3 < s.bytes.size := by
            rw [s.bytes_size_eq]; unfold iendOffset; omega
          have hPos : iendOffset s + 8 ≤ s.bytes.size := by
            rw [s.bytes_size_eq]; unfold iendOffset; omega
          have hReadIend := s.readChunk_multiIdat_iend hLen
          have hSeenIDAT : (stateAfterIdatsM s i).seenIDAT = true := by
            unfold stateAfterIdatsM
            simp
            rw [hin]
            cases hChunks : s.idatChunks with
            | nil => exact absurd hChunks s.hNonempty
            | cons _ _ => simp
          have hHeader : (stateAfterIdatsM s i).header = some s.header := rfl
          have hIdatEq : (stateAfterIdatsM s i).idat = s.idatData := by
            rw [hin]
            exact stateAfterIdatsM_idat_full s
          have hMetaEq :
              (stateAfterIdatsM s i).metadata = PngMetadata.empty := rfl
          have hRes := parsePngLoopFuelWithMetadata_iend_success_step fuel' s.bytes
            (iendOffset s) (stateAfterIdatsM s i) s.header hPos hLen hReadIend
            hHeader hSeenIDAT
          rw [hIdatEq, hMetaEq] at hRes
          exact hRes
  | succ k ih =>
      have hilt : i < s.idatChunks.length := by omega
      cases fuel with
      | zero =>
          have : s.idatChunks.length - i + 1 ≤ 0 := hFuel
          omega
      | succ fuel' =>
          have hi' : i + 1 ≤ s.idatChunks.length := by omega
          have hk' : s.idatChunks.length - (i + 1) = k := by omega
          have hFuel' : s.idatChunks.length - (i + 1) + 1 ≤ fuel' := by
            have hkfuel : s.idatChunks.length - i + 1 ≤ fuel' + 1 := hFuel
            omega
          have hRest := ih (i := i + 1) hi' fuel' hFuel' hk'
          exact parsePngLoopFuelWithMetadata_walk_idat_step s i hilt fuel' hRest

set_option maxHeartbeats 1200000 in
/-- Metadata-aware analogue of `parsePngLoopFuel_walk_ihdr_step`: from
the empty initial state at byte 8, after one fuel unit the loop
transitions through IHDR into the state after 0 IDATs, then walks the
whole chunk sequence. -/
lemma parsePngLoopFuelWithMetadata_walk_ihdr_step (s : MultiIdatContainerSpec) (fuel : Nat)
    (hFuel : s.idatChunks.length + 1 ≤ fuel)
    (hHeader : (encodeIHDRData s.header).size < 2 ^ 32 := by decide) :
    parsePngLoopFuelWithMetadata (fuel + 1) s.bytes 8
      { header := none, idat := ByteArray.empty,
        seenPLTE := false, seenIDAT := false, closedIDAT := false,
        metadata := PngMetadata.empty } =
      some { header := s.header, idat := s.idatData,
             metadata := PngMetadata.empty } := by
  have hPos : (8 : Nat) + 8 ≤ s.bytes.size := by
    rw [s.bytes_size_eq]; unfold idatTotalWireSize
    have hmono := idatPrefixWireSize_mono s.idatChunks 0 s.idatChunks.length (by omega)
    omega
  have hLen : (8 : Nat) + 3 < s.bytes.size := by omega
  have hReadIhdr := s.readChunk_multiIdat_ihdr hLen
  have hIhdrSize : (encodeIHDRData s.header).size = 13 := encodeIHDRData_size s.header
  have hCT256 : s.header.colorType < 256 := by
    rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide
  have hBDlt : s.header.bitDepth < 256 := by
    rcases s.hBitDepth with h | h | h <;> rw [h] <;> decide
  have hParseHdr := parseIHDRData_encodeIHDRData_lt256 s.header
    s.hWidth s.hHeight hBDlt s.hInterlace hCT256
  conv => lhs; unfold parsePngLoopFuelWithMetadata
  have hReadU32Len : readU32BE s.bytes 8 hLen = 13 := by
    have hExtractLen : s.bytes.extract 8 (8 + 4) = u32be 13 := by
      have h := s.bytes_extract_ihdr
      have hChunkLen := mkChunkBytes_extract_len ihdrTypeBytes (encodeIHDRData s.header)
      rw [hIhdrSize] at hChunkLen
      have hsub : (s.bytes.extract 8 (8 + 12 + (encodeIHDRData s.header).size)).extract 0 4 =
          (mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)).extract 0 4 := by
        rw [h]
      rw [hChunkLen] at hsub
      have hExt := ByteArray.extract_extract (a := s.bytes) (i := 8)
        (j := 8 + 12 + (encodeIHDRData s.header).size) (k := 0) (l := 4)
      have hMin : min (8 + 4) (8 + 12 + (encodeIHDRData s.header).size) = 8 + 4 := by
        rw [hIhdrSize]; omega
      rw [hMin] at hExt
      rw [← hExt]
      exact hsub
    exact readU32BE_of_extract_eq s.bytes 8 13 hLen hExtractLen (by decide)
  simp [hPos, hLen, hReadIhdr, hReadU32Len, hParseHdr]
  have hOffsetEq : (33 : Nat) = idatOffset s 0 := by
    unfold idatOffset idatPrefixWireSize
    simp
  have hStateEq :
      ({ header := some s.header, idat := ByteArray.empty,
         seenPLTE := false, seenIDAT := false, closedIDAT := false,
         metadata := PngMetadata.empty } : PngMetadataParseState) =
      stateAfterIdatsM s 0 := by
    unfold stateAfterIdatsM
    simp [List.foldl]
  rw [hOffsetEq, hStateEq]
  refine ⟨by decide, ?_⟩
  exact parsePngLoopFuelWithMetadata_walk_idats_aux s 0 (by omega) fuel
    (by omega)

/-! ### parsePngSimple eliminator for length ≥ 2

When the spec has two or more IDAT chunks, the fast-path `parsePngSimple`
returns `none` because its third `readChunk` reads the *second* IDAT
chunk's type bytes (rather than `iendTypeBytes`), failing the IEND-type
check. -/

set_option maxHeartbeats 1600000 in
/-- For a multi-IDAT spec with at least two IDAT chunks, `parsePngSimple`
returns `none`. Used by the main theorem to dispatch into the
`parsePngLoopFuel` walk. -/
private lemma parsePngSimple_eq_none_of_multi (s : MultiIdatContainerSpec)
    (hLen2 : 2 ≤ s.idatChunks.length) :
    parsePngSimple s.bytes s.bytes_size_ge_8 = none := by
  unfold parsePngSimple
  -- Membership facts.
  have hPos0 : 0 < s.idatChunks.length := by omega
  have hPos1 : 1 < s.idatChunks.length := by omega
  have hMem0 : s.idatChunks[0] ∈ s.idatChunks := List.getElem_mem hPos0
  have hMem1 : s.idatChunks[1] ∈ s.idatChunks := List.getElem_mem hPos1
  have hCS0 := s.hChunkSize s.idatChunks[0] hMem0
  have hCS1 := s.hChunkSize s.idatChunks[1] hMem1
  -- Prefix-size values.
  have hPref0 : idatPrefixWireSize s.idatChunks 0 = 0 := by
    unfold idatPrefixWireSize; simp
  have hPref1 :
      idatPrefixWireSize s.idatChunks 1 = 12 + s.idatChunks[0].size := by
    rw [idatPrefixWireSize_succ s.idatChunks 0 hPos0, hPref0]
  have hPref2 :
      idatPrefixWireSize s.idatChunks 2 =
        24 + s.idatChunks[0].size + s.idatChunks[1].size := by
    rw [idatPrefixWireSize_succ s.idatChunks 1 hPos1, hPref1]; omega
  have hMonoFull :
      idatPrefixWireSize s.idatChunks 2 ≤ idatTotalWireSize s := by
    unfold idatTotalWireSize
    exact idatPrefixWireSize_mono s.idatChunks 2 s.idatChunks.length (by omega)
  -- Position bounds.
  have hLen1 : (8 : Nat) + 3 < s.bytes.size := by rw [s.bytes_size_eq]; omega
  have hLen2' : (33 : Nat) + 3 < s.bytes.size := by rw [s.bytes_size_eq]; omega
  have hLen3' : (45 + s.idatChunks[0].size : Nat) + 3 < s.bytes.size := by
    rw [s.bytes_size_eq]; omega
  -- Signature.
  have hSig : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
  -- IHDR read at 8.
  have hRead1 := s.readChunk_multiIdat_ihdr hLen1
  -- IDAT[0] read at byte 33 via the kernel (avoids dependent-type rewrites).
  have hRead2 : readChunk s.bytes 33 hLen2' =
      some (idatTypeBytes, s.idatChunks[0], 45 + s.idatChunks[0].size) := by
    have hWrap : s.bytes.extract 33 (33 + 12 + s.idatChunks[0].size) =
        mkChunkBytes idatTypeBytes s.idatChunks[0] := by
      have h0 := s.bytes_extract_idat_at 0 hPos0
      have hO0 : idatOffset s 0 = 33 := by unfold idatOffset; rw [hPref0]
      have hO1 : idatOffset s 1 = 33 + 12 + s.idatChunks[0].size := by
        unfold idatOffset; rw [hPref1]; omega
      rw [hO0, hO1] at h0; exact h0
    have hRange : (33 : Nat) + 12 + s.idatChunks[0].size ≤ s.bytes.size := by
      rw [s.bytes_size_eq]; omega
    have h := readChunk_at_mkChunkBytes s.bytes 33 idatTypeBytes s.idatChunks[0]
      (by rfl) hCS0 hWrap hRange hLen2'
    rw [show (33 + 8 + s.idatChunks[0].size + 4 : Nat) =
              45 + s.idatChunks[0].size from by omega] at h
    exact h
  -- IDAT[1] read at byte (45 + chunk_0.size) via the kernel.
  have hRead3 :
      readChunk s.bytes (45 + s.idatChunks[0].size) hLen3' =
        some (idatTypeBytes, s.idatChunks[1],
          45 + s.idatChunks[0].size + 8 + s.idatChunks[1].size + 4) := by
    have hWrap : s.bytes.extract (45 + s.idatChunks[0].size)
        (45 + s.idatChunks[0].size + 12 + s.idatChunks[1].size) =
        mkChunkBytes idatTypeBytes s.idatChunks[1] := by
      have h1 := s.bytes_extract_idat_at 1 hPos1
      have hO1 : idatOffset s 1 = 45 + s.idatChunks[0].size := by
        unfold idatOffset; rw [hPref1]; omega
      have hO2 : idatOffset s 2 =
          45 + s.idatChunks[0].size + 12 + s.idatChunks[1].size := by
        unfold idatOffset; rw [hPref2]; omega
      rw [hO1, hO2] at h1; exact h1
    have hRange : 45 + s.idatChunks[0].size + 12 + s.idatChunks[1].size ≤ s.bytes.size := by
      rw [s.bytes_size_eq]; omega
    exact readChunk_at_mkChunkBytes s.bytes (45 + s.idatChunks[0].size)
      idatTypeBytes s.idatChunks[1] (by rfl) hCS1 hWrap hRange hLen3'
  -- Type bytes inequality.
  have hIdatNeIend : (idatTypeBytes != iendTypeBytes) = true := by decide
  -- IHDR round-trip.
  have hCT256 : s.header.colorType < 256 := by
    rcases s.hColorType with h | h | h | h <;> rw [h] <;> decide
  have hBDlt : s.header.bitDepth < 256 := by
    rcases s.hBitDepth with h | h | h <;> rw [h] <;> decide
  have hParseHdr := parseIHDRData_encodeIHDRData_lt256 s.header
    s.hWidth s.hHeight hBDlt s.hInterlace hCT256
  have hCtBdOk :
      pngColorTypeBitDepthSupported s.header.colorType s.header.bitDepth = true :=
    s.hCtBdSupported
  have hCTProp :
      ¬s.header.colorType = 0 → ¬s.header.colorType = 2 →
        ¬s.header.colorType = 4 → s.header.colorType = 6 := by
    intro h0 h2 h4
    rcases s.hColorType with hc | hc | hc | hc
    · exact (h0 hc).elim
    · exact (h2 hc).elim
    · exact (h4 hc).elim
    · exact hc
  -- Drive parsePngSimple's body to the IEND-type check, which fails.
  simp [hSig, hLen1, hRead1, hParseHdr, hCtBdOk,
        hLen2', hRead2, hLen3', hRead3, hIdatNeIend,
        bne_self_eq_false' (a := ihdrTypeBytes)]

/-! ### Main theorem: parsePng for multi-IDAT spec -/

set_option maxHeartbeats 1600000 in
/-- The general multi-IDAT forward correctness theorem: `parsePng`
accepts any byte stream matching `MultiIdatContainerSpec` and returns
the header + concatenated IDAT data. -/
theorem parsePng_multiIdatContainerSpec_correct (s : MultiIdatContainerSpec) :
    parsePng s.bytes s.bytes_size_ge_8 = some (s.header, s.idatData) := by
  -- Case split on the chunks list.
  match hChunks : s.idatChunks with
  | [] => exact absurd hChunks s.hNonempty
  | [data] =>
      -- Singleton case: reduce via the singleton lemma.
      have hMem : data ∈ s.idatChunks := by
        rw [hChunks]; exact List.mem_singleton.mpr rfl
      exact parsePng_multiIdatContainerSpec_correct_of_singleton data hChunks
        (s.hChunkSize data hMem)
  | c1 :: c2 :: rest =>
      -- Length ≥ 2 case: parsePngSimple returns none, fall through to loop.
      have hLen2 : 2 ≤ s.idatChunks.length := by rw [hChunks]; simp
      have hSimpleNone : parsePngSimple s.bytes s.bytes_size_ge_8 = none :=
        parsePngSimple_eq_none_of_multi s hLen2
      have hSigExtract : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
      have hSigCheck : (s.bytes.extract 0 8 != pngSignature) = false := by
        rw [hSigExtract]; exact bne_self_eq_false' (a := pngSignature)
      have hLoopFuel : s.idatChunks.length + 1 ≤ s.bytes.size := by
        rw [s.bytes_size_eq]
        unfold idatTotalWireSize idatPrefixWireSize
        rw [List.take_length]
        have hSum : 12 * s.idatChunks.length ≤
            s.idatChunks.foldl (fun acc c => acc + 12 + c.size) 0 := by
          have aux : ∀ (acc : Nat) (chunks : List ByteArray),
              acc + 12 * chunks.length ≤
                chunks.foldl (fun a c => a + 12 + c.size) acc := by
            intro acc chunks
            induction chunks generalizing acc with
            | nil => simp
            | cons d ds ih =>
                simp only [List.length_cons, List.foldl_cons]
                have h := ih (acc + 12 + d.size)
                have : acc + 12 * (ds.length + 1) ≤
                    acc + 12 + d.size + 12 * ds.length := by omega
                exact Nat.le_trans this h
          have h := aux 0 s.idatChunks
          simpa using h
        omega
      have hHeader : (encodeIHDRData s.header).size < 2 ^ 32 := by
        rw [encodeIHDRData_size s.header]; decide
      unfold parsePng
      simp [hSimpleNone, hSigCheck]
      exact parsePngLoopFuel_walk_ihdr_step s s.bytes.size hLoopFuel hHeader

/-! ### Metadata-aware main theorem (Phase 6c) -/

/-- When `parsePngSimple` returns `none` (e.g., for multi-IDAT streams),
`parsePngSimpleWithMetadata` returns `none` as well. -/
private lemma parsePngSimpleWithMetadata_eq_none_of_simple_none
    (bytes : ByteArray) (h : 8 ≤ bytes.size)
    (hSimple : parsePngSimple bytes h = none) :
    parsePngSimpleWithMetadata bytes h = none := by
  unfold parsePngSimpleWithMetadata
  simp [hSimple]

/-- Singleton-case adapter: when `idatChunks = [data]`, `parsePngForDecode`
returns the simple result. Closes the multi-IDAT main theorem's `length = 1`
case by routing through `parsePng_simpleContainerSpec_correct`. -/
private lemma parsePngForDecode_multiIdatContainerSpec_correct_of_singleton
    {s : MultiIdatContainerSpec} (data : ByteArray)
    (h : s.idatChunks = [data])
    (hIdatSize : data.size < 2 ^ 32) :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := PngMetadata.empty } := by
  let simple : SimpleContainerSpec :=
    { header := s.header, idatData := data,
      hBitDepth := s.hBitDepth, hColorType := s.hColorType,
      hCtBdSupported := s.hCtBdSupported,
      hInterlace := s.hInterlace, hWidth := s.hWidth, hHeight := s.hHeight }
  have hBytes : s.bytes = simple.bytes :=
    bytes_eq_simple_of_singleton data h
  have hDataEq : s.idatData = data := idatData_of_singleton data h
  have hSimple :
      parsePngSimple simple.bytes simple.bytes_size_ge_8 =
        some (simple.header, simple.idatData) :=
    parsePngSimple_simpleContainerSpec_correct simple hIdatSize
  -- Pull s.bytes' parsePngForDecode to simple.bytes via hBytes.
  have hCongr :
      parsePngForDecode s.bytes s.bytes_size_ge_8 =
        parsePngForDecode simple.bytes simple.bytes_size_ge_8 := by congr 1
  rw [hCongr, hDataEq]
  unfold parsePngForDecode parsePngSimpleWithMetadata
  simp [hSimple]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 1600000 in
/-- The metadata-aware multi-IDAT main theorem: `parsePngForDecode`
accepts any byte stream matching `MultiIdatContainerSpec` and returns
the header + concatenated IDAT data + empty metadata. -/
theorem parsePngForDecode_multiIdatContainerSpec_correct (s : MultiIdatContainerSpec) :
    parsePngForDecode s.bytes s.bytes_size_ge_8 =
      some { header := s.header, idat := s.idatData,
             metadata := PngMetadata.empty } := by
  match hChunks : s.idatChunks with
  | [] => exact absurd hChunks s.hNonempty
  | [data] =>
      have hMem : data ∈ s.idatChunks := by
        rw [hChunks]; exact List.mem_singleton.mpr rfl
      exact parsePngForDecode_multiIdatContainerSpec_correct_of_singleton data hChunks
        (s.hChunkSize data hMem)
  | c1 :: c2 :: rest =>
      have hLen2 : 2 ≤ s.idatChunks.length := by rw [hChunks]; simp
      have hSimpleNone : parsePngSimple s.bytes s.bytes_size_ge_8 = none :=
        parsePngSimple_eq_none_of_multi s hLen2
      have hSimpleMetaNone :
          parsePngSimpleWithMetadata s.bytes s.bytes_size_ge_8 = none :=
        parsePngSimpleWithMetadata_eq_none_of_simple_none s.bytes s.bytes_size_ge_8
          hSimpleNone
      have hSigExtract : s.bytes.extract 0 8 = pngSignature := s.bytes_extract_signature
      have hSigCheck : (s.bytes.extract 0 8 != pngSignature) = false := by
        rw [hSigExtract]; exact bne_self_eq_false' (a := pngSignature)
      have hLoopFuel : s.idatChunks.length + 1 ≤ s.bytes.size := by
        rw [s.bytes_size_eq]
        unfold idatTotalWireSize idatPrefixWireSize
        rw [List.take_length]
        have hSum : 12 * s.idatChunks.length ≤
            s.idatChunks.foldl (fun acc c => acc + 12 + c.size) 0 := by
          have aux : ∀ (acc : Nat) (chunks : List ByteArray),
              acc + 12 * chunks.length ≤
                chunks.foldl (fun a c => a + 12 + c.size) acc := by
            intro acc chunks
            induction chunks generalizing acc with
            | nil => simp
            | cons d ds ih =>
                simp only [List.length_cons, List.foldl_cons]
                have h := ih (acc + 12 + d.size)
                have : acc + 12 * (ds.length + 1) ≤
                    acc + 12 + d.size + 12 * ds.length := by omega
                exact Nat.le_trans this h
          have h := aux 0 s.idatChunks
          simpa using h
        omega
      have hHeader : (encodeIHDRData s.header).size < 2 ^ 32 := by
        rw [encodeIHDRData_size s.header]; decide
      unfold parsePngForDecode parsePngWithMetadata
      simp [hSimpleMetaNone, hSigCheck]
      exact parsePngLoopFuelWithMetadata_walk_ihdr_step s s.bytes.size hLoopFuel hHeader

end MultiIdatContainerSpec

/-! ## Simple → multi adapter (Phase 5↔6 bridge)

Every `SimpleContainerSpec` is the singleton case of a
`MultiIdatContainerSpec`: lifting wraps `idatData` into a one-element
`idatChunks` list. Combined with `bytes_eq_simple_of_singleton`, this
makes `decodeBitmap_external_correct` derivable as a corollary of the
multi-IDAT theorem. -/

/-- Lift a `SimpleContainerSpec` to a singleton `MultiIdatContainerSpec`.
Requires the u32 length-field fit (`s.idatData.size < 2^32`), the same
side condition Phase 5's `decodeBitmap_external_correct` carries via
`ExternalPngSpec.hIdatSize`. -/
def SimpleContainerSpec.toMulti (s : SimpleContainerSpec)
    (hSize : s.idatData.size < 2 ^ 32) : MultiIdatContainerSpec where
  header := s.header
  idatChunks := [s.idatData]
  hChunkSize := by
    intro c hMem
    rw [List.mem_singleton] at hMem
    rw [hMem]; exact hSize
  hNonempty := by simp
  hBitDepth := s.hBitDepth
  hColorType := s.hColorType
  hCtBdSupported := s.hCtBdSupported
  hInterlace := s.hInterlace
  hWidth := s.hWidth
  hHeight := s.hHeight

/-- The lifted multi-spec's bytes equal the original simple-spec's bytes. -/
lemma SimpleContainerSpec.toMulti_bytes (s : SimpleContainerSpec)
    (hSize : s.idatData.size < 2 ^ 32) :
    (s.toMulti hSize).bytes = s.bytes := by
  have hChunks : (s.toMulti hSize).idatChunks = [s.idatData] := rfl
  have h := MultiIdatContainerSpec.bytes_eq_simple_of_singleton
    (s := s.toMulti hSize) s.idatData hChunks
  -- The auxiliary simple built inside the lemma has the same fields as `s`.
  show (s.toMulti hSize).bytes = s.bytes
  rw [h]
  -- The inner `SimpleContainerSpec.mk ...` matches `s` field-by-field.
  rfl

/-- The lifted multi-spec's concatenated IDAT payload equals the simple
spec's `idatData`. -/
lemma SimpleContainerSpec.toMulti_idatData (s : SimpleContainerSpec)
    (hSize : s.idatData.size < 2 ^ 32) :
    (s.toMulti hSize).idatData = s.idatData :=
  MultiIdatContainerSpec.idatData_of_singleton s.idatData rfl

end Lemmas

end Bitmaps
