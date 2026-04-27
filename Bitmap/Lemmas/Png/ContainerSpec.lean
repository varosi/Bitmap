import Bitmap.Lemmas.Png.ChunkValidation
import Bitmap.Lemmas.Png.EncodeDecodeBase

namespace Bitmaps

namespace Lemmas

open Png

/-! ## PNG container forward-correctness spec (Phase 3)

A declarative spec for the PNG container layer — the byte structure
above zlib/DEFLATE that the runtime `parsePng` accepts. Phase 3a (this
commit) covers the minimal-shape spec corresponding to `parsePngSimple`:
the 8-byte signature, one `IHDR` chunk, one `IDAT` chunk, and a final
empty `IEND` chunk. This is exactly the shape `encodeBitmap` produces
and the shape `parsePngSimple` validates in one pass.

A later commit will extend the spec to multiple `IDAT` chunks and
tolerated ancillary chunks (`gAMA`, `pHYs`, `tEXt`, …), proving forward
correctness through `parsePngLoopFuel` and the existing
`ChunkValidation.lean` lemmas. -/

/-- Encode a `PngHeader` into the 13-byte IHDR data payload, inverse to
`parseIHDRData`. The header order is:

  bytes 0-3   : width (BE u32)
  bytes 4-7   : height (BE u32)
  byte  8     : bit depth
  byte  9     : color type
  byte  10    : compression method (always 0)
  byte  11    : filter method (always 0)
  byte  12    : interlace method (always 0) -/
def encodeIHDRData (h : PngHeader) : ByteArray :=
  u32be h.width ++ u32be h.height
    ++ ByteArray.mk #[u8 h.bitDepth, u8 h.colorType, u8 0, u8 0, u8 0]

/-- The simple-shape container spec: 8-byte signature, one IHDR, one
IDAT carrying `idatData` payload bytes, and one empty IEND. The header
is constrained to the supported subset (`bitDepth = 8` and
`colorType ∈ {0,2,6}`) so the runtime accepts it. -/
structure SimpleContainerSpec where
  header : PngHeader
  idatData : ByteArray
  hBitDepth : header.bitDepth = 8
  hColorType : header.colorType = 0 ∨ header.colorType = 2 ∨ header.colorType = 6
  hWidth : header.width < 2 ^ 32
  hHeight : header.height < 2 ^ 32

/-- The on-the-wire bytes of a simple container: the PNG signature
followed by IHDR, IDAT, IEND chunks (each with a CRC computed by
`mkChunkBytes`). -/
def SimpleContainerSpec.bytes (s : SimpleContainerSpec) : ByteArray :=
  pngSignature
    ++ mkChunkBytes ihdrTypeBytes (encodeIHDRData s.header)
    ++ mkChunkBytes idatTypeBytes s.idatData
    ++ mkChunkBytes iendTypeBytes ByteArray.empty

/-- The byte stream of any simple-container spec is at least 8 bytes long
(it carries the PNG signature). This is the size precondition required
by `parsePng`. -/
lemma SimpleContainerSpec.bytes_size_ge_8 (s : SimpleContainerSpec) :
    8 ≤ s.bytes.size := by
  unfold SimpleContainerSpec.bytes
  simp [pngSignature_size, ByteArray.size_append]
  omega

/-- The encoded IHDR data has exactly 13 bytes — 4 (width) + 4 (height) + 5
(bit depth + color type + compression + filter + interlace). -/
lemma encodeIHDRData_size (h : PngHeader) : (encodeIHDRData h).size = 13 := by
  unfold encodeIHDRData
  have hTail : (ByteArray.mk #[u8 h.bitDepth, u8 h.colorType, u8 0, u8 0, u8 0]).size = 5 := rfl
  simp [u32be_size, ByteArray.size_append, hTail]

end Lemmas

end Bitmaps
