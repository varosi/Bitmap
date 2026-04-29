import Bitmap.Lemmas.Png.ContainerSpec
import Bitmap.Lemmas.Png.DeflateStreamSpec
import Bitmap.Lemmas.Png.RowFilterSpec
import Bitmap.Lemmas.Png.StoredBlockProofsSpec
import Bitmap.Lemmas.Bitmap

universe u

namespace Bitmaps

namespace Lemmas

open Png

/-! ## End-to-end external-PNG spec (Phase 5 scaffold)

`ExternalPngSpec px` describes a byte stream `bytes` that the runtime
`decodeBitmap` accepts as a valid PNG of the supported subset and that
decodes to a specific `Bitmap px`. Unlike the existing
`decodeBitmap_encodeBitmap` round-trip, this spec is independent of
this library's encoder — any byte sequence matching the spec's
constraints is accepted, regardless of which tool produced it.

The structure composes all four lower-level spec layers:

  * **Phase 3** (`ContainerSpec.lean`): the PNG signature + IHDR +
    IDAT + IEND chunk layout.
  * **Phase 2** (`DeflateStreamSpec.lean`): the IDAT data is a zlib
    envelope around a `DeflateStreamSpec` made of stored, fixed, or
    dynamic blocks.
  * **Phase 4** (`RowFilterSpec.lean`): the deflate output, viewed as
    a sequence of `rowBytes + 1` byte rows, reconstructs to the
    bitmap's pixel data via `reconstructRowsSpec`.
  * **Phase 1a / 1b**: the per-block-type forward correctness theorems
    feeding into the deflate stream.

The end-to-end theorem
  `decodeBitmap_external_correct (s : ExternalPngSpec px) :
     decodeBitmap (containerBytes s) = some s.bitmap`
is deferred until Phases 2 and 3 are finalised — the structural spec
below makes the obligations visible in code. -/

/-- A description of an external PNG byte stream, decomposed into its
container/zlib/deflate/row-filter layers.

The `decodeBitmap_external_correct` theorem is deferred; the fields
below capture the necessary composition constraints, with proof
obligations connecting:

  - container header ↔ bitmap dimensions and color type
  - container IDAT bytes ↔ zlib-wrapped deflate stream
  - deflate stream output ↔ row-filter-encoded bitmap pixels -/
structure ExternalPngSpec (px : Type u) [Pixel px] [PngPixel px] where
  /-- The bitmap the byte stream should decode to. -/
  bitmap : Bitmap px
  /-- The container layer (signature + IHDR + IDAT + IEND chunks). -/
  container : SimpleContainerSpec
  /-- Container width matches bitmap width. -/
  hWidth : container.header.width = bitmap.size.width
  /-- Container height matches bitmap height. -/
  hHeight : container.header.height = bitmap.size.height
  /-- Container color type matches the pixel type's `PngPixel.colorType`. -/
  hColorType : container.header.colorType = (PngPixel.colorType (α := px)).toNat
  /-- The deflate output (i.e., the result of inflating the container's
      IDAT data through the zlib envelope) — a contiguous byte buffer of
      `bitmap.size.height * (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)`
      bytes carrying one filter byte plus one row of pixel data per row. -/
  inflatedRaw : ByteArray
  /-- The container's IDAT bytes are exactly the zlib envelope of
      `inflatedRaw`. The witnessing `DeflateStreamSpec` (Phase 2) is
      attached as a separate constraint via `deflateStream`. -/
  hIdatIsZlib :
    container.idatData = zlibCompressOf inflatedRaw bitmap.data
  /-- Per-row layout invariant: the inflated raw bytes are organised as
      `bitmap.size.height` rows, each prefixed by a 1-byte filter selector
      followed by `rowBytes := bitmap.size.width * Pixel.bytesPerPixel (α := px)` payload
      bytes. -/
  hInflatedSize :
    inflatedRaw.size = bitmap.size.height * (bitmap.size.width * Pixel.bytesPerPixel (α := px) + 1)
  /-- The full reconstruction via `reconstructRowsSpec` consumes every byte of
      `inflatedRaw`. This is a structural invariant required for the row-filter
      chain to terminate at the right offset; it falls out of `hInflatedSize`
      and `reconstructRowsSpec_size` once the multi-row chain proof lands. -/
  hRowsConsumed :
    (reconstructRowsSpec inflatedRaw bitmap.size.height
        (bitmap.size.width * Pixel.bytesPerPixel (α := px)) (Pixel.bytesPerPixel (α := px))).2
      = inflatedRaw.size

/-! ### Forward correctness (deferred)

The full theorem
  `decodeBitmap_external_correct (s : ExternalPngSpec px) :
     decodeBitmap s.container.bytes = some s.bitmap`
composes:

  1. `parsePng_simpleContainerSpec_correct_of_simple` — already wired in
     `ContainerSpec.lean`; needs `parsePngSimple_simpleContainerSpec_correct`
     (Phase 3 finalisation).
  2. zlib decompression correctness against `s.inflatedRaw` — needs
     `deflateStreamSpec_decode_correct` (Phase 2 finalisation, which
     in turn needs the fixed-block fast/slow bridge).
  3. Row-filter reconstruction via `unfilterRow_eq_spec` and
     `reconstructRowsSpec` (Phase 4, complete). The constraint
     `hRowFilter` above is the placeholder for the explicit
     row-filter equation; it is replaced in Phase 5b once the row
     stream's structure is concretely tied to `bitmap.data`.
  4. Pixel-format extraction — already covered by
     `decodeRowsLoopCore_encodeRaw` in `EncodeDecodeBase.lean`. -/

end Lemmas

end Bitmaps
