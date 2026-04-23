import Bitmap.Lemmas.Png.ZlibEnvelope

namespace Bitmaps

namespace Lemmas

namespace ZlibFixedHelpers

open Png
open U32Helpers

/-- Records the byte-size layout of the fixed zlib wrapper so later proofs do not import the full base file. -/
lemma zlibFixedWrapper_size (raw : ByteArray) :
    (zlibCompressFixed raw).size = (deflateFixed raw).size + 6 := by
  rw [zlibCompressFixed_eq]; exact zlibCompressOf_size _ _

/-- Gives the fixed zlib wrapper a stable lower bound for header and Adler checks. -/
lemma zlibFixedWrapper_size_ge (raw : ByteArray) :
    6 ≤ (zlibCompressFixed raw).size := by
  rw [zlibCompressFixed_eq]; exact zlibCompressOf_size_ge _ _

/-- Exposes the fixed zlib header bytes directly, avoiding a dependency on the heavier encode/decode umbrella file. -/
lemma zlibFixedWrapper_cmf_flg (raw : ByteArray) :
    let bytes := zlibCompressFixed raw
    let h0 : 0 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 0 < 6) (zlibFixedWrapper_size_ge raw)
    let h1 : 1 < bytes.size := by
      exact lt_of_lt_of_le (by decide : 1 < 6) (zlibFixedWrapper_size_ge raw)
    bytes[0]'h0 = u8 0x78 ∧ bytes[1]'h1 = u8 0x01 :=
  zlibCompressOf_cmf_flg (deflated := deflateFixed raw) (raw := raw)

/-- Extracts the deflated payload from the fixed zlib wrapper without replaying unrelated base proofs. -/
lemma zlibFixedWrapper_extract_deflated (raw : ByteArray) :
    (zlibCompressFixed raw).extract 2 ((zlibCompressFixed raw).size - 4) = deflateFixed raw := by
  rw [zlibCompressFixed_eq]; exact zlibCompressOf_extract_deflated _ _

/-- Extracts the Adler32 trailer from the fixed zlib wrapper for the final checksum check. -/
lemma zlibFixedWrapper_extract_adler (raw : ByteArray) :
    (zlibCompressFixed raw).extract ((zlibCompressFixed raw).size - 4)
        ((zlibCompressFixed raw).size - 4 + 4) = u32be (adler32 raw).toNat := by
  rw [zlibCompressFixed_eq]; exact zlibCompressOf_extract_adler _ _

end ZlibFixedHelpers

end Lemmas

end Bitmaps
