import Bitmap.Lemmas.Png.CoreByteArray
import Bitmap.Lemmas.Png.EncodeDecodeBaseU32

namespace Bitmaps

namespace Lemmas

namespace ZlibFixedHelpers

open Png
open U32Helpers

/-- `emptyWithCapacity` is extensionally empty, so wrapper proofs can ignore the reserved buffer. -/
private lemma emptyWithCapacity_eq_empty_local (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty := by
  rfl

/-- Records the byte-size layout of the fixed zlib wrapper so later proofs do not import the full base file. -/
lemma zlibFixedWrapper_size (raw : ByteArray) :
    (zlibCompressFixed raw).size = (deflateFixed raw).size + 6 := by
  unfold zlibCompressFixed
  have hheader : (ByteArray.mk #[u8 0x78, u8 0x01]).size = 2 := by decide
  simp [ByteArray.size_append, u32be_size, hheader, emptyWithCapacity_eq_empty_local]
  omega

/-- Gives the fixed zlib wrapper a stable lower bound for header and Adler checks. -/
lemma zlibFixedWrapper_size_ge (raw : ByteArray) :
    6 ≤ (zlibCompressFixed raw).size := by
  have hsz : (zlibCompressFixed raw).size = (deflateFixed raw).size + 6 :=
    zlibFixedWrapper_size raw
  have h6 : 6 ≤ (deflateFixed raw).size + 6 := Nat.le_add_left _ _
  rw [hsz]
  exact h6

set_option maxHeartbeats 5000000 in
/-- Exposes the fixed zlib header bytes directly, avoiding a dependency on the heavier encode/decode umbrella file. -/
lemma zlibFixedWrapper_cmf_flg (raw : ByteArray) :
    let bytes := zlibCompressFixed raw
    let h0 : 0 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 0 < 6) (zlibFixedWrapper_size_ge raw)
    let h1 : 1 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 1 < 6) (zlibFixedWrapper_size_ge raw)
    bytes[0]'h0 = u8 0x78 ∧ bytes[1]'h1 = u8 0x01 := by
  let bytes := zlibCompressFixed raw
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateFixed raw
  let adler := u32be (adler32 raw).toNat
  have h0h : 0 < header.size := by decide
  have h1h : 1 < header.size := by decide
  have h0 : 0 < bytes.size := by
    exact lt_of_lt_of_le (by decide : 0 < 6) (zlibFixedWrapper_size_ge raw)
  have h1 : 1 < bytes.size := by
    exact lt_of_lt_of_le (by decide : 1 < 6) (zlibFixedWrapper_size_ge raw)
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
  have hheader0 : header[0]'h0h = u8 0x78 := by
    rfl
  have hheader1 : header[1]'h1h = u8 0x01 := by
    rfl
  have hget0' : bytes[0]'h0 = u8 0x78 := by
    simpa [bytes, zlibCompressFixed, emptyWithCapacity_eq_empty_local, hget0, hheader0]
  have hget1' : bytes[1]'h1 = u8 0x01 := by
    simpa [bytes, zlibCompressFixed, emptyWithCapacity_eq_empty_local, hget1, hheader1]
  exact ⟨hget0', hget1'⟩

set_option maxHeartbeats 5000000 in
/-- Extracts the deflated payload from the fixed zlib wrapper without replaying unrelated base proofs. -/
lemma zlibFixedWrapper_extract_deflated (raw : ByteArray) :
    (zlibCompressFixed raw).extract 2 ((zlibCompressFixed raw).size - 4) = deflateFixed raw := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateFixed raw
  let adler := u32be (adler32 raw).toNat
  have hheader : header.size = 2 := by decide
  have hadler : adler.size = 4 := by
    simpa using (u32be_size (adler32 raw).toNat)
  have hsize'' : header.size + deflated.size + adler.size - 4 = deflated.size + 2 := by
    simp [hheader, hadler]
    omega
  calc
    (zlibCompressFixed raw).extract 2 ((zlibCompressFixed raw).size - 4)
        = (header ++ deflated ++ adler).extract 2 (header.size + deflated.size + adler.size - 4) := by
            simp [zlibCompressFixed, header, deflated, adler, ByteArray.size_append, hheader, hadler,
              emptyWithCapacity_eq_empty_local]
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

set_option maxHeartbeats 5000000 in
/-- Extracts the Adler32 trailer from the fixed zlib wrapper for the final checksum check. -/
lemma zlibFixedWrapper_extract_adler (raw : ByteArray) :
    (zlibCompressFixed raw).extract ((zlibCompressFixed raw).size - 4)
        ((zlibCompressFixed raw).size - 4 + 4) = u32be (adler32 raw).toNat := by
  let header : ByteArray := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateFixed raw
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
    (zlibCompressFixed raw).extract ((zlibCompressFixed raw).size - 4)
        ((zlibCompressFixed raw).size - 4 + 4)
        = (header ++ deflated ++ adler).extract (header.size + deflated.size + adler.size - 4)
            (header.size + deflated.size + adler.size - 4 + 4) := by
              simp [zlibCompressFixed, header, deflated, adler, ByteArray.size_append, hheader, hadler,
                emptyWithCapacity_eq_empty_local]
    _ = (header ++ deflated ++ adler).extract (deflated.size + 2) (deflated.size + 2 + 4) := by
          simp [hsize'']
    _ = adler.extract 0 adler.size := by
          have h :=
            (ByteArray.extract_append_size_add
              (a := header ++ deflated) (b := adler) (i := 0) (j := adler.size))
          simpa [hprefix, hadler, ByteArray.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    _ = adler := by
          simp [ByteArray.extract_zero_size]

end ZlibFixedHelpers

end Lemmas

end Bitmaps
