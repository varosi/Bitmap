import Bitmap.Lemmas.Png.CoreByteArray
import Bitmap.Lemmas.Png.EncodeDecodeBaseU32

namespace Bitmaps

namespace Lemmas

open Png
open U32Helpers

/- Proof-layer abstraction for `zlibCompress{Stored,Fixed,Dynamic}`. These three
   runtime defs share the same zlib envelope shape — header ++ deflate ++ adler —
   and differ only in which deflate function is plugged in. `zlibCompressOf`
   takes the already-deflated payload as an argument so that structural lemmas
   about the envelope can be proved once and reused across all three variants. -/
def zlibCompressOf (deflated raw : ByteArray) : ByteArray :=
  let header := ByteArray.mk #[u8 0x78, u8 0x01]
  let adler := u32be (adler32 raw).toNat
  let outSize := header.size + deflated.size + adler.size
  let out := ByteArray.emptyWithCapacity outSize
  out ++ header ++ deflated ++ adler

lemma zlibCompressStored_eq (raw : ByteArray) :
    zlibCompressStored raw = zlibCompressOf (deflateStored raw) raw := rfl

lemma zlibCompressFixed_eq (raw : ByteArray) :
    zlibCompressFixed raw = zlibCompressOf (deflateFixed raw) raw := rfl

lemma zlibCompressDynamic_eq (raw : ByteArray) :
    zlibCompressDynamic raw = zlibCompressOf (deflateDynamic raw) raw := rfl

/- Local simp attribute so the envelope unfolds to a plain `header ++ deflated ++ adler`
   append — `emptyWithCapacity` is extensionally empty for any capacity. Kept private
   so callers outside this file pick up the public `emptyWithCapacity_eq_empty` from
   `EncodeDecodeBase.lean` unchanged. -/
private lemma zlibEnvelope_emptyWithCapacity_eq_empty (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty := rfl

-- The zlib envelope begins with the fixed two-byte header.
lemma zlibCompressOf_header (deflated raw : ByteArray) :
    (zlibCompressOf deflated raw).extract 0 2 = ByteArray.mk #[u8 0x78, u8 0x01] := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let adler := u32be (adler32 raw).toNat
  have hsize : header.size = 2 := by decide
  have hprefix :
      (header ++ deflated ++ adler).extract 0 2 = header.extract 0 2 := by
    apply byteArray_extract_append_prefix (a := header) (b := deflated ++ adler) (n := 2)
    simp [hsize]
  have hheader : header.extract 0 2 = header := by
    rw [← hsize, ByteArray.extract_zero_size]
  simp [zlibCompressOf, header, adler, hprefix, hheader,
    zlibEnvelope_emptyWithCapacity_eq_empty, ByteArray.empty_append]

-- Size of the zlib envelope is header (2) + deflate + adler32 (4).
lemma zlibCompressOf_size (deflated raw : ByteArray) :
    (zlibCompressOf deflated raw).size = deflated.size + 6 := by
  unfold zlibCompressOf
  have hheader : (ByteArray.mk #[u8 0x78, u8 0x01]).size = 2 := by decide
  simp [ByteArray.size_append, u32be_size, hheader,
    zlibEnvelope_emptyWithCapacity_eq_empty, ByteArray.empty_append]
  omega

-- The zlib envelope always has at least the 2-byte header and 4-byte Adler32.
lemma zlibCompressOf_size_ge (deflated raw : ByteArray) :
    6 ≤ (zlibCompressOf deflated raw).size := by
  have hsz := zlibCompressOf_size deflated raw
  have h6 : 6 ≤ deflated.size + 6 := Nat.le_add_left _ _
  rw [hsz]
  exact h6

-- The first two bytes of the zlib envelope are the CMF/FLG constants `0x78 0x01`.
lemma zlibCompressOf_cmf_flg (deflated raw : ByteArray) :
    let bytes := zlibCompressOf deflated raw
    let h0 : 0 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 0 < 6) (zlibCompressOf_size_ge deflated raw)
    let h1 : 1 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 1 < 6) (zlibCompressOf_size_ge deflated raw)
    bytes[0]'h0 = u8 0x78 ∧ bytes[1]'h1 = u8 0x01 := by
  let bytes := zlibCompressOf deflated raw
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let adler := u32be (adler32 raw).toNat
  have h0h : 0 < header.size := by decide
  have h1h : 1 < header.size := by decide
  have h0 : 0 < bytes.size := by
    exact lt_of_lt_of_le (by decide : 0 < 6) (zlibCompressOf_size_ge deflated raw)
  have h1 : 1 < bytes.size := by
    exact lt_of_lt_of_le (by decide : 1 < 6) (zlibCompressOf_size_ge deflated raw)
  have hle : header.size ≤ (header ++ deflated ++ adler).size := by
    simp [ByteArray.size_append]
    omega
  have h0' : 0 < (header ++ deflated ++ adler).size := lt_of_lt_of_le h0h hle
  have h1' : 1 < (header ++ deflated ++ adler).size := lt_of_lt_of_le h1h hle
  have hget0 :
      (header ++ deflated ++ adler)[0]'h0' = header[0]'h0h := by
    have hget := ByteArray.get_append_left (a := header) (b := deflated ++ adler) (i := 0) h0h
    simpa [ByteArray.append_assoc] using hget
  have hget1 :
      (header ++ deflated ++ adler)[1]'h1' = header[1]'h1h := by
    have hget := ByteArray.get_append_left (a := header) (b := deflated ++ adler) (i := 1) h1h
    simpa [ByteArray.append_assoc] using hget
  have hheader0 : header[0]'h0h = u8 0x78 := by rfl
  have hheader1 : header[1]'h1h = u8 0x01 := by rfl
  have hget0' : bytes[0]'h0 = u8 0x78 := by
    simpa [bytes, zlibCompressOf, zlibEnvelope_emptyWithCapacity_eq_empty,
      ByteArray.empty_append, hget0, hheader0]
  have hget1' : bytes[1]'h1 = u8 0x01 := by
    simpa [bytes, zlibCompressOf, zlibEnvelope_emptyWithCapacity_eq_empty,
      ByteArray.empty_append, hget1, hheader1]
  exact ⟨hget0', hget1'⟩

-- The zlib envelope's payload window (bytes 2..size-4) is exactly the deflate stream.
lemma zlibCompressOf_extract_deflated (deflated raw : ByteArray) :
    (zlibCompressOf deflated raw).extract 2 ((zlibCompressOf deflated raw).size - 4) = deflated := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let adler := u32be (adler32 raw).toNat
  have hheader : header.size = 2 := by decide
  have hadler : adler.size = 4 := by
    simpa using (u32be_size (adler32 raw).toNat)
  have hsize'' : header.size + deflated.size + adler.size - 4 = deflated.size + 2 := by
    simp [hheader, hadler]
    omega
  calc
    (zlibCompressOf deflated raw).extract 2 ((zlibCompressOf deflated raw).size - 4)
        = (header ++ deflated ++ adler).extract 2 (header.size + deflated.size + adler.size - 4) := by
            simp [zlibCompressOf, header, adler, ByteArray.size_append, hheader, hadler,
              zlibEnvelope_emptyWithCapacity_eq_empty, ByteArray.empty_append]
    _ = (header ++ deflated ++ adler).extract 2 (deflated.size + 2) := by
          simp [hsize'']
    _ = (deflated ++ adler).extract 0 deflated.size := by
          have h :=
            (ByteArray.extract_append_size_add
              (a := header) (b := deflated ++ adler) (i := 0) (j := deflated.size))
          simpa [hheader, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    _ = deflated := by
          have hprefix :
              (deflated ++ adler).extract 0 deflated.size = deflated.extract 0 deflated.size := by
            exact byteArray_extract_append_prefix (a := deflated) (b := adler) (n := deflated.size) (by exact le_rfl)
          simp [hprefix, ByteArray.extract_zero_size]

-- The zlib envelope's Adler32 trailer (bytes size-4..size) is exactly `u32be (adler32 raw)`.
lemma zlibCompressOf_extract_adler (deflated raw : ByteArray) :
    (zlibCompressOf deflated raw).extract ((zlibCompressOf deflated raw).size - 4)
        ((zlibCompressOf deflated raw).size - 4 + 4) = u32be (adler32 raw).toNat := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let adler := u32be (adler32 raw).toNat
  have hheader : header.size = 2 := by decide
  have hadler : adler.size = 4 := by
    simpa using (u32be_size (adler32 raw).toNat)
  have hsize'' : header.size + deflated.size + adler.size - 4 = deflated.size + 2 := by
    simp [hheader, hadler]
    omega
  have hprefix : (header ++ deflated).size = deflated.size + 2 := by
    simp [ByteArray.size_append, hheader, Nat.add_comm]
  calc
    (zlibCompressOf deflated raw).extract ((zlibCompressOf deflated raw).size - 4)
        ((zlibCompressOf deflated raw).size - 4 + 4)
        = (header ++ deflated ++ adler).extract (header.size + deflated.size + adler.size - 4)
            (header.size + deflated.size + adler.size - 4 + 4) := by
              simp [zlibCompressOf, header, adler, ByteArray.size_append, hheader, hadler,
                zlibEnvelope_emptyWithCapacity_eq_empty, ByteArray.empty_append]
    _ = (header ++ deflated ++ adler).extract (deflated.size + 2) (deflated.size + 2 + 4) := by
          simp [hsize'']
    _ = adler.extract 0 adler.size := by
          have h :=
            (ByteArray.extract_append_size_add
              (a := header ++ deflated) (b := adler) (i := 0) (j := adler.size))
          simpa [hprefix, hadler, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    _ = adler := by
          simp [ByteArray.extract_zero_size]

end Lemmas

end Bitmaps
