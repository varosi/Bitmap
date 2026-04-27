import Bitmap.Lemmas.Png.EncodeDecodeBase

namespace Bitmaps

namespace Lemmas

open Png

/-! ## Row-filter reconstruction spec

A declarative spec for PNG filter-byte reconstruction (RFC 2083 §6.2). The
runtime `unfilterRow` is implemented as an `Id.run do` for-loop with a
mutable accumulator; the spec layer expresses the same computation as a
pure `List.foldl` over the row indices, which is easier to reason about
inductively. The forward-correctness theorem `unfilterRow_eq_spec` ties the
two together; downstream proofs (Phases 3-5) treat `reconstructRowSpec` as
the canonical row reconstruction. -/

/-- Per-byte filter formula. The five filter types are exactly those defined
by RFC 2083 §6.2; any out-of-range filter byte falls through to `raw` (the
parser never invokes this case because `unfilterRow` is gated by `filter.toNat ≤ 4`). -/
def reconstructByteAt (filter : UInt8) (raw a b c : UInt8) : UInt8 :=
  match filter.toNat with
  | 0 => raw
  | 1 => u8 (raw.toNat + a.toNat)
  | 2 => u8 (raw.toNat + b.toNat)
  | 3 => u8 (raw.toNat + ((a.toNat + b.toNat) / 2))
  | 4 => u8 (raw.toNat + paethPredictor a.toNat b.toNat c.toNat)
  | _ => raw

/-- One step of the row reconstruction fold. The body intentionally mirrors
the inlined form of the runtime's `Id.run do` loop in `unfilterRow`, so the
forward-correctness theorem reduces to a `forIn → foldl` rewrite plus
`rfl`. The decoupled byte formula `reconstructByteAt` is unfolded inline
here; the lemma `reconstructRowStep_eq_byteAt` exposes the factored form
for downstream proofs. -/
def reconstructRowStep (filter : UInt8) (row prev : ByteArray) (bpp : Nat)
    (out : ByteArray) (i : Nat) : ByteArray :=
  let raw := row.get! i
  let a := if bpp ≤ i then out.get! (i - bpp) else (0 : UInt8)
  let b := if i < prev.size then prev.get! i else (0 : UInt8)
  let c := if bpp ≤ i ∧ i < prev.size then prev.get! (i - bpp) else (0 : UInt8)
  let recon :=
    match filter.toNat with
    | 0 => raw
    | 1 => u8 (raw.toNat + a.toNat)
    | 2 => u8 (raw.toNat + b.toNat)
    | 3 => u8 (raw.toNat + ((a.toNat + b.toNat) / 2))
    | 4 => u8 (raw.toNat + paethPredictor a.toNat b.toNat c.toNat)
    | _ => raw
  out.push recon

/-- Decoupled view of the step: the pushed byte equals
`reconstructByteAt filter raw a b c` for the inputs read at index `i`. -/
lemma reconstructRowStep_eq_byteAt (filter : UInt8) (row prev : ByteArray) (bpp : Nat)
    (out : ByteArray) (i : Nat) :
    reconstructRowStep filter row prev bpp out i =
      out.push (reconstructByteAt filter (row.get! i)
        (if bpp ≤ i then out.get! (i - bpp) else (0 : UInt8))
        (if i < prev.size then prev.get! i else (0 : UInt8))
        (if bpp ≤ i ∧ i < prev.size then prev.get! (i - bpp) else (0 : UInt8))) := by
  unfold reconstructRowStep reconstructByteAt
  rfl

/-- Pure spec for `unfilterRow`: fold `reconstructRowStep` over the row
indices `0, 1, …, row.size - 1`, starting from an empty accumulator. -/
def reconstructRowSpec (filter : UInt8) (row prev : ByteArray) (bpp : Nat) : ByteArray :=
  (List.range' 0 row.size 1).foldl (reconstructRowStep filter row prev bpp) ByteArray.empty

/-- Forward correctness: the runtime `unfilterRow` equals the pure spec.
The proof unfolds the runtime's `Id.run do` for-loop into a `List.foldl`
using `Std.Legacy.Range.forIn_eq_forIn_range'`; the loop body is then
literally `reconstructRowStep`. -/
theorem unfilterRow_eq_spec (filter : UInt8) (row prev : ByteArray) (bpp : Nat)
    (hfilter : filter.toNat ≤ 4) :
    unfilterRow filter row prev bpp hfilter = reconstructRowSpec filter row prev bpp := by
  unfold unfilterRow reconstructRowSpec reconstructRowStep
  simp [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

/-- A push-and-fold preserves length: `(foldl push)` over a list of any
size adds exactly that size to the accumulator's length. Generic helper
shared with `reconstructRowSpec_size`. -/
private lemma foldl_pushStep_size
    (xs : List Nat) (f : ByteArray → Nat → UInt8) (out : ByteArray) :
    (xs.foldl (fun out i => out.push (f out i)) out).size = out.size + xs.length := by
  induction xs generalizing out with
  | nil => simp
  | cons i xs ih =>
      have ih' := ih (out := out.push (f out i))
      simpa [ByteArray.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih'

/-- The pure spec preserves row length. Proved directly without going
through the runtime, so callers do not need a `filter.toNat ≤ 4` premise. -/
lemma reconstructRowSpec_size (filter : UInt8) (row prev : ByteArray) (bpp : Nat) :
    (reconstructRowSpec filter row prev bpp).size = row.size := by
  unfold reconstructRowSpec reconstructRowStep
  simpa using foldl_pushStep_size (List.range' 0 row.size 1)
    (fun out i =>
      reconstructByteAt filter (row.get! i)
        (if bpp ≤ i then out.get! (i - bpp) else (0 : UInt8))
        (if i < prev.size then prev.get! i else (0 : UInt8))
        (if bpp ≤ i ∧ i < prev.size then prev.get! (i - bpp) else (0 : UInt8)))
    ByteArray.empty

/-! ### Multi-row reconstruction spec

The decoder's `decodeRowsLoopCore` consumes a serialized PNG IDAT-content
stream — `rowBytes + 1` bytes per row, where the first byte is the filter
selector and the remaining `rowBytes` are the (filtered) row payload. This
spec describes the row-by-row reconstruction independent of color-channel
conversion, so downstream proofs can chain it with the pixel-format
extraction step. -/

/-- One step of the rows fold: read the filter byte at `offset`, extract
the row payload of length `rowBytes`, reconstruct it against `prev`, and
return the new previous row plus the advanced offset. The state threaded
through the fold is `(prev, offset)`. -/
def reconstructRowsStep (raw : ByteArray) (rowBytes bpp : Nat)
    (state : ByteArray × Nat) (_y : Nat) : ByteArray × Nat :=
  let (prev, offset) := state
  let filter := raw.get! offset
  let offset := offset + 1
  let rowData := raw.extract offset (offset + rowBytes)
  let row := reconstructRowSpec filter rowData prev bpp
  (row, offset + rowBytes)

/-- Pure spec for the multi-row reconstruction: fold `reconstructRowsStep`
over `0, 1, …, h - 1`, starting from the empty previous row at offset 0,
and return the final previous-row reconstruction together with the
end-of-stream offset. The decoder additionally copies each reconstructed
row into a destination pixel buffer; that color-extraction step is the
subject of Phase 5 and is not part of this spec. -/
def reconstructRowsSpec (raw : ByteArray) (h rowBytes bpp : Nat) : ByteArray × Nat :=
  (List.range h).foldl (reconstructRowsStep raw rowBytes bpp) (ByteArray.empty, 0)

end Lemmas

end Bitmaps
