import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.BinaryRec
import Init.Tactics
import Init.Data.Array.Lemmas
import Init.Data.Array.Set
import Init.Data.ByteArray
import Lean

deriving instance Repr for ByteArray

open Lean
open System (FilePath)

instance : ToJson ByteArray where
  toJson bs := Json.arr <| bs.data.map (fun b => toJson b.toNat)

instance : FromJson ByteArray where
  fromJson? j := do
    let arr ← j.getArr?
    let mut out := ByteArray.empty
    for v in arr do
      let n : Nat ← fromJson? v
      if n < 256 then
        out := out.push (UInt8.ofNat n)
      else
        throw s!"byte out of range: {n}"
    return out

instance : ToJson UInt16 where
  toJson n := toJson n.toNat

instance : FromJson UInt16 where
  fromJson? j := do
    let n : Nat ← fromJson? j
    if n < 2 ^ 16 then
      return UInt16.ofNat n
    else
      throw s!"uint16 out of range: {n}"

universe u

namespace Bitmaps

structure Size where
  width  : ℕ
  height : ℕ
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

-------------------------------------------------------------------------------
-- A single color pixel of RGB values of any type
structure PixelRGB (RangeT : Type u) where
  mk ::
  r : RangeT
  g : RangeT
  b : RangeT
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

instance instInhabitedPixelRGB (RangeT) [Inhabited RangeT] : Inhabited (PixelRGB RangeT) where
  default := { r := default, g := default, b := default }

instance instToJsonPixelRGB (RangeT) [ToJson RangeT] : ToJson (PixelRGB RangeT) where
  toJson
    | ⟨r, g, b⟩ =>
      Json.mkObj [
        ("r", toJson r),
        ("g", toJson g),
        ("b", toJson b)
      ]

instance instFromJsonPixelRGB (RangeT) [FromJson RangeT] : FromJson (PixelRGB RangeT) where
  fromJson? j := do
    let r ← j.getObjValAs? RangeT "r"
    let g ← j.getObjValAs? RangeT "g"
    let b ← j.getObjValAs? RangeT "b"
    return { r, g, b }

-- Simple addition of intensities of two pixels
instance {α : Type} [Add α] : Add (PixelRGB α) where
  add p1 p2 := { r := p1.r + p2.r, g := p1.g + p2.g, b := p1.b + p2.b }

instance {α : Type} [Mul α] : Mul (PixelRGB α) where
  mul p1 p2 := { r := p1.r * p2.r, g := p1.g * p2.g, b := p1.b * p2.b }

def PixelRGB8  := PixelRGB UInt8
def PixelRGB16 := PixelRGB UInt16

-------------------------------------------------------------------------------
-- A single color pixel of RGBA values of any type
structure PixelRGBA (RangeT : Type u) where
  mk ::
  r : RangeT
  g : RangeT
  b : RangeT
  a : RangeT
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

instance instInhabitedPixelRGBA (RangeT) [Inhabited RangeT] : Inhabited (PixelRGBA RangeT) where
  default := { r := default, g := default, b := default, a := default }

instance instToJsonPixelRGBA (RangeT) [ToJson RangeT] : ToJson (PixelRGBA RangeT) where
  toJson
    | ⟨r, g, b, a⟩ =>
      Json.mkObj [
        ("r", toJson r),
        ("g", toJson g),
        ("b", toJson b),
        ("a", toJson a)
      ]

instance instFromJsonPixelRGBA (RangeT) [FromJson RangeT] : FromJson (PixelRGBA RangeT) where
  fromJson? j := do
    let r ← j.getObjValAs? RangeT "r"
    let g ← j.getObjValAs? RangeT "g"
    let b ← j.getObjValAs? RangeT "b"
    let a ← j.getObjValAs? RangeT "a"
    return { r, g, b, a }

-- Simple addition of intensities of two pixels
instance (priority := low) {α : Type} [Add α] : Add (PixelRGBA α) where
  add p1 p2 := { r := p1.r + p2.r, g := p1.g + p2.g, b := p1.b + p2.b, a := p1.a + p2.a }

instance (priority := low) {α : Type} [Mul α] : Mul (PixelRGBA α) where
  mul p1 p2 := { r := p1.r * p2.r, g := p1.g * p2.g, b := p1.b * p2.b, a := p1.a * p2.a }

def PixelRGBA8  := PixelRGBA UInt8
def PixelRGBA16 := PixelRGBA UInt16

class AlphaChannel (RangeT : Type u) extends NatCast RangeT where
  toNat : RangeT → Nat
  maxValue : Nat

instance : AlphaChannel UInt8 where
  natCast := UInt8.ofNat
  toNat := UInt8.toNat
  maxValue := 255

instance : AlphaChannel UInt16 where
  natCast := UInt16.ofNat
  toNat := UInt16.toNat
  maxValue := 65535

@[inline] def alphaDivRound (num den : Nat) : Nat :=
  if den = 0 then
    0
  else
    (num + den / 2) / den

@[inline] def alphaClamp {RangeT : Type u} [AlphaChannel RangeT] (n : Nat) : RangeT :=
  Nat.cast (R := RangeT) (Nat.min (AlphaChannel.maxValue (RangeT := RangeT)) n)

@[inline] def alphaMulNorm {RangeT : Type u} [AlphaChannel RangeT]
    (x y : RangeT) : RangeT :=
  let max := (AlphaChannel.maxValue (RangeT := RangeT))
  alphaClamp (alphaDivRound (AlphaChannel.toNat x * AlphaChannel.toNat y) max)

@[inline] def alphaOver {RangeT : Type u} [AlphaChannel RangeT]
    (dstA srcA : RangeT) : RangeT :=
  let src := AlphaChannel.toNat srcA
  let dst := AlphaChannel.toNat dstA
  let max := (AlphaChannel.maxValue (RangeT := RangeT))
  let outA := src + alphaDivRound (dst * (max - src)) max
  alphaClamp outA

@[inline] def blendChannelOver {RangeT : Type u} [AlphaChannel RangeT]
    (dstC srcC dstA srcA : RangeT) : RangeT :=
  let src := AlphaChannel.toNat srcA
  let dst := AlphaChannel.toNat dstA
  let max := (AlphaChannel.maxValue (RangeT := RangeT))
  let outA := src + alphaDivRound (dst * (max - src)) max
  if outA = 0 then
    alphaClamp 0
  else
    let srcPremul := AlphaChannel.toNat srcC * src
    let dstPremul := alphaDivRound (AlphaChannel.toNat dstC * dst * (max - src)) max
    alphaClamp (alphaDivRound ((srcPremul + dstPremul) * max) outA)

-- Alpha compositing: `src` over `dst`.
@[inline] def rgbaOver {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) : PixelRGBA RangeT :=
  let outA := alphaOver dst.a src.a
  { r := blendChannelOver dst.r src.r dst.a src.a
    g := blendChannelOver dst.g src.g dst.a src.a
    b := blendChannelOver dst.b src.b dst.a src.a
    a := outA }

-- Multiply blend mode composed as `src` over `dst`.
@[inline] def rgbaMultiplyOver {RangeT : Type u} [AlphaChannel RangeT]
    (dst src : PixelRGBA RangeT) : PixelRGBA RangeT :=
  let srcMul : PixelRGBA RangeT :=
    { r := alphaMulNorm dst.r src.r
      g := alphaMulNorm dst.g src.g
      b := alphaMulNorm dst.b src.b
      a := src.a }
  rgbaOver dst srcMul

instance {RangeT : Type u} [AlphaChannel RangeT] : Add (PixelRGBA RangeT) where
  add dst src := rgbaOver dst src

instance {RangeT : Type u} [AlphaChannel RangeT] : Mul (PixelRGBA RangeT) where
  mul dst src := rgbaMultiplyOver dst src

-------------------------------------------------------------------------------
-- A single grayscale pixel of any type
structure PixelGray (RangeT : Type u) where
  mk ::
  v : RangeT
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

instance instInhabitedPixelGray (RangeT) [Inhabited RangeT] : Inhabited (PixelGray RangeT) where
  default := { v := default }

instance instToJsonPixelGray (RangeT) [ToJson RangeT] : ToJson (PixelGray RangeT) where
  toJson
    | ⟨v⟩ =>
      Json.mkObj [
        ("v", toJson v)
      ]

instance instFromJsonPixelGray (RangeT) [FromJson RangeT] : FromJson (PixelGray RangeT) where
  fromJson? j := do
    let v ← j.getObjValAs? RangeT "v"
    return { v }

instance {α : Type} [Add α] : Add (PixelGray α) where
  add p1 p2 := { v := p1.v + p2.v }

instance {α : Type} [Mul α] : Mul (PixelGray α) where
  mul p1 p2 := { v := p1.v * p2.v }

def PixelGray8 := PixelGray UInt8
def PixelGray16 := PixelGray UInt16

-------------------------------------------------------------------------------
-- A single grayscale pixel with alpha of any type
structure PixelGrayAlpha (RangeT : Type u) where
  mk ::
  v : RangeT
  a : RangeT
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

instance instInhabitedPixelGrayAlpha (RangeT) [Inhabited RangeT] :
    Inhabited (PixelGrayAlpha RangeT) where
  default := { v := default, a := default }

instance instToJsonPixelGrayAlpha (RangeT) [ToJson RangeT] :
    ToJson (PixelGrayAlpha RangeT) where
  toJson
    | ⟨v, a⟩ =>
      Json.mkObj [
        ("v", toJson v),
        ("a", toJson a)
      ]

instance instFromJsonPixelGrayAlpha (RangeT) [FromJson RangeT] :
    FromJson (PixelGrayAlpha RangeT) where
  fromJson? j := do
    let v ← j.getObjValAs? RangeT "v"
    let a ← j.getObjValAs? RangeT "a"
    return { v, a }

instance {α : Type} [Add α] : Add (PixelGrayAlpha α) where
  add p1 p2 := { v := p1.v + p2.v, a := p1.a + p2.a }

instance {α : Type} [Mul α] : Mul (PixelGrayAlpha α) where
  mul p1 p2 := { v := p1.v * p2.v, a := p1.a * p2.a }

def PixelGrayAlpha8 := PixelGrayAlpha UInt8
def PixelGrayAlpha16 := PixelGrayAlpha UInt16

instance : Inhabited PixelRGB8 := instInhabitedPixelRGB _
instance : DecidableEq PixelRGB8 := by
  unfold PixelRGB8
  infer_instance

instance : Inhabited PixelRGB16 := instInhabitedPixelRGB _
instance : DecidableEq PixelRGB16 := by
  unfold PixelRGB16
  infer_instance

instance : Inhabited PixelRGBA8 := instInhabitedPixelRGBA _
instance : DecidableEq PixelRGBA8 := by
  unfold PixelRGBA8
  infer_instance

instance : Inhabited PixelRGBA16 := instInhabitedPixelRGBA _
instance : DecidableEq PixelRGBA16 := by
  unfold PixelRGBA16
  infer_instance

instance : Inhabited PixelGray8 := instInhabitedPixelGray _
instance : DecidableEq PixelGray8 := by
  unfold PixelGray8
  infer_instance

instance : Inhabited PixelGray16 := instInhabitedPixelGray _
instance : DecidableEq PixelGray16 := by
  unfold PixelGray16
  infer_instance

instance : Inhabited PixelGrayAlpha8 := instInhabitedPixelGrayAlpha _
instance : DecidableEq PixelGrayAlpha8 := by
  unfold PixelGrayAlpha8
  infer_instance

instance : Inhabited PixelGrayAlpha16 := instInhabitedPixelGrayAlpha _
instance : DecidableEq PixelGrayAlpha16 := by
  unfold PixelGrayAlpha16
  infer_instance

-------------------------------------------------------------------------------
-- Pixel metadata for byte layout.
class Pixel (α : Type u) where
  bytesPerPixel : Nat
  bytesPerPixel_pos : 0 < bytesPerPixel
  read : (data : ByteArray) -> (base : Nat) ->
    (h : base + (bytesPerPixel - 1) < data.size) -> α
  write : (data : ByteArray) -> (base : Nat) ->
    (h : base + (bytesPerPixel - 1) < data.size) -> α -> ByteArray
  write_size : ∀ (data : ByteArray) (base : Nat)
    (h : base + (bytesPerPixel - 1) < data.size) (px : α),
    (write data base h px).size = data.size
  read_write :
    ∀ (data : ByteArray) (base : Nat)
      (h : base + (bytesPerPixel - 1) < data.size) (px : α),
      read (write data base h px) base
        (by simpa [write_size (data := data) (base := base) (h := h) (px := px)] using h) = px

def bytesPerPixelRGB : Nat := 3
def bytesPerPixelRGBA : Nat := 4
def bytesPerPixelGray : Nat := 1
def bytesPerPixelGrayAlpha : Nat := 2
def bytesPerPixelRGB16 : Nat := 6
def bytesPerPixelRGBA16 : Nat := 8
def bytesPerPixelGray16 : Nat := 2
def bytesPerPixelGrayAlpha16 : Nat := 4

@[inline] def u16HighByte (x : UInt16) : UInt8 :=
  UInt8.ofNat (x.toNat / 256)

@[inline] def u16LowByte (x : UInt16) : UInt8 :=
  UInt8.ofNat x.toNat

/-- Splitting a `UInt16` into big-endian bytes and reading it back is identity.
This is the arithmetic core reused by every 16-bit pixel layout proof. -/
private theorem u16_from_be_bytes (x : UInt16) :
    UInt16.ofNat ((u16HighByte x).toNat * 256 + (u16LowByte x).toNat) = x := by
  unfold u16HighByte u16LowByte
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat']
  have hx : x.toNat < 2 ^ 16 := UInt16.toNat_lt x
  have hdivLt : x.toNat / 256 < 256 := by omega
  rw [Nat.mod_eq_of_lt hdivLt]
  have hrec : x.toNat / 256 * 256 + x.toNat % 256 = x.toNat := by
    have h := Nat.div_add_mod x.toNat 256
    omega
  rw [hrec]
  exact UInt16.ofNat_toNat

/-- Converting an 8-bit byte to `UInt16` preserves its numeric value.
This lets the 16-bit byte reconstruction proof survive UInt normalization. -/
private theorem u8_toUInt16_toNat (x : UInt8) : x.toUInt16.toNat = x.toNat := by
  cases x
  simp [UInt8.toUInt16, UInt8.toNat, UInt16.toNat]

/-- The same reconstruction fact after Lean normalizes `UInt16.ofNat`.
It closes goals produced by simplifying big-endian byte reads. -/
private theorem u16_from_be_bytes_uint16 (x : UInt16) :
    (u16HighByte x).toUInt16 * 256 + (u16LowByte x).toUInt16 = x := by
  apply UInt16.toNat_inj.mp
  simp [UInt16.toNat_add, UInt16.toNat_mul, UInt16.toNat_ofNat]
  unfold u16HighByte u16LowByte
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat']
  have hx : x.toNat < 2 ^ 16 := UInt16.toNat_lt x
  have hdivLt : x.toNat / 256 < 256 := by omega
  rw [Nat.mod_eq_of_lt hdivLt]
  have hrec : x.toNat / 256 * 256 + x.toNat % 256 = x.toNat := by
    have h := Nat.div_add_mod x.toNat 256
    omega
  rw [hrec]
  omega

/-- Setting one byte keeps the byte array size.
The 16-bit pixel writers use it after each big-endian byte write. -/
private theorem byteArray_set_size {bs : ByteArray} {i : Nat} (hi : i < bs.size) {v : UInt8} :
    (bs.set i v hi).size = bs.size := by
  cases bs with
  | mk arr =>
      simp [ByteArray.set, ByteArray.size, Array.size_set]

/-- A byte write at another index does not affect a read.
This packages the array-level `set_ne` fact for multi-byte pixel proofs. -/
private theorem byteArray_get_set_ne {bs : ByteArray} {i j : Nat}
    (hi : i < bs.size) (hj : j < bs.size) (hij : i ≠ j) {v : UInt8}
    (h' : j < (bs.set i v hi).size) :
    (bs.set i v hi).get j h' = bs.get j hj := by
  cases bs with
  | mk arr =>
      simpa [ByteArray.set, ByteArray.get] using
        (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj)
          (h := hij))

def readU16BEAt (data : ByteArray) (base : Nat)
    (h : base + 1 < data.size) : UInt16 := by
  have h0 : base < data.size := by omega
  exact UInt16.ofNat ((data.get base h0).toNat * 256 + (data.get (base + 1) h).toNat)

def writeU16BEAt (data : ByteArray) (base : Nat)
    (h : base + 1 < data.size) (x : UInt16) : ByteArray := by
  have h0 : base < data.size := by omega
  let data1 := data.set base (u16HighByte x) h0
  have hsize1 : data1.size = data.size := by
    simpa [data1] using (byteArray_set_size (bs := data) (i := base) (hi := h0)
      (v := u16HighByte x))
  have h1 : base + 1 < data1.size := by
    simpa [hsize1] using h
  exact data1.set (base + 1) (u16LowByte x) h1

/-- Writing a big-endian `UInt16` sample preserves the byte buffer size.
It is the size side condition used by 16-bit pixel instances. -/
private theorem writeU16BEAt_size
    (data : ByteArray) (base : Nat) (h : base + 1 < data.size) (x : UInt16) :
    (writeU16BEAt data base h x).size = data.size := by
  unfold writeU16BEAt
  simp [byteArray_set_size]

/-- Reading the same two-byte slot just written returns the written `UInt16`.
This is the sample-level read/write law lifted to 16-bit pixels. -/
private theorem readU16BEAt_write_same
    (data : ByteArray) (base : Nat) (h : base + 1 < data.size) (x : UInt16) :
    readU16BEAt (writeU16BEAt data base h x) base
      (by simpa [writeU16BEAt_size (data := data) (base := base) (h := h) (x := x)] using h) = x := by
  have h0 : base < data.size := by omega
  let data1 := data.set base (u16HighByte x) h0
  have hsize1 : data1.size = data.size := by
    simpa [data1] using (byteArray_set_size (bs := data) (i := base) (hi := h0)
      (v := u16HighByte x))
  have h1 : base + 1 < data1.size := by
    simpa [hsize1] using h
  let data2 := data1.set (base + 1) (u16LowByte x) h1
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size := by
      simpa [data2] using (byteArray_set_size (bs := data1) (i := base + 1)
        (hi := h1) (v := u16LowByte x))
    simpa [hsize1] using hsize2'
  have h0d1 : base < data1.size := by
    simpa [hsize1] using h0
  have h0d2 : base < data2.size := by
    simpa [hsize2] using h0
  have h1d2 : base + 1 < data2.size := by
    simpa [hsize2] using h
  have hhi : data2.get base h0d2 = u16HighByte x := by
    have hkeep : data2.get base h0d2 = data1.get base h0d1 := by
      simpa [data2] using
        (byteArray_get_set_ne (bs := data1) (i := base + 1) (j := base)
          (hi := h1) (hj := h0d1) (hij := by omega) (v := u16LowByte x)
          (h' := h0d2))
    have hset : data1.get base h0d1 = u16HighByte x := by
      simp [data1, ByteArray.set, ByteArray.get]
    simp [hkeep, hset]
  have hlo : data2.get (base + 1) h1d2 = u16LowByte x := by
    simp [data2, ByteArray.set, ByteArray.get]
  unfold readU16BEAt writeU16BEAt
  simp [data1, data2, hhi, hlo, u16_from_be_bytes_uint16]

/-- A later non-overlapping two-byte write preserves an earlier `UInt16` read.
This keeps RGB/RGBA component proofs small when writing several samples. -/
private theorem readU16BEAt_write_after
    (data : ByteArray) (readBase writeBase : Nat)
    (hread : readBase + 1 < data.size) (hwrite : writeBase + 1 < data.size)
    (x : UInt16) (hbefore : readBase + 1 < writeBase) :
    readU16BEAt (writeU16BEAt data writeBase hwrite x) readBase
      (by simpa [writeU16BEAt_size (data := data) (base := writeBase) (h := hwrite) (x := x)] using hread) =
    readU16BEAt data readBase hread := by
  have hr0 : readBase < data.size := by omega
  have hw0 : writeBase < data.size := by omega
  let data1 := data.set writeBase (u16HighByte x) hw0
  have hsize1 : data1.size = data.size := by
    simpa [data1] using (byteArray_set_size (bs := data) (i := writeBase)
      (hi := hw0) (v := u16HighByte x))
  have hw1 : writeBase + 1 < data1.size := by
    simpa [hsize1] using hwrite
  let data2 := data1.set (writeBase + 1) (u16LowByte x) hw1
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size := by
      simpa [data2] using (byteArray_set_size (bs := data1) (i := writeBase + 1)
        (hi := hw1) (v := u16LowByte x))
    simpa [hsize1] using hsize2'
  have hr0d1 : readBase < data1.size := by simpa [hsize1] using hr0
  have hr1d1 : readBase + 1 < data1.size := by simpa [hsize1] using hread
  have hr0d2 : readBase < data2.size := by simpa [hsize2] using hr0
  have hr1d2 : readBase + 1 < data2.size := by simpa [hsize2] using hread
  have h0keep : data2.get readBase hr0d2 = data.get readBase hr0 := by
    have h2 : data2.get readBase hr0d2 = data1.get readBase hr0d1 := by
      simpa [data2] using
        (byteArray_get_set_ne (bs := data1) (i := writeBase + 1) (j := readBase)
          (hi := hw1) (hj := hr0d1) (hij := by omega) (v := u16LowByte x)
          (h' := hr0d2))
    have h1 : data1.get readBase hr0d1 = data.get readBase hr0 := by
      simpa [data1] using
        (byteArray_get_set_ne (bs := data) (i := writeBase) (j := readBase)
          (hi := hw0) (hj := hr0) (hij := by omega) (v := u16HighByte x)
          (h' := hr0d1))
    simp [h2, h1]
  have h1keep : data2.get (readBase + 1) hr1d2 = data.get (readBase + 1) hread := by
    have h2 : data2.get (readBase + 1) hr1d2 = data1.get (readBase + 1) hr1d1 := by
      simpa [data2] using
        (byteArray_get_set_ne (bs := data1) (i := writeBase + 1) (j := readBase + 1)
          (hi := hw1) (hj := hr1d1) (hij := by omega) (v := u16LowByte x)
          (h' := hr1d2))
    have h1 : data1.get (readBase + 1) hr1d1 = data.get (readBase + 1) hread := by
      simpa [data1] using
        (byteArray_get_set_ne (bs := data) (i := writeBase) (j := readBase + 1)
          (hi := hw0) (hj := hread) (hij := by omega) (v := u16HighByte x)
          (h' := hr1d1))
    simp [h2, h1]
  unfold readU16BEAt writeU16BEAt
  simp [data1, data2, h0keep, h1keep]

/-- An earlier non-overlapping two-byte write preserves a later `UInt16` read.
This is the symmetric preservation fact for multi-component 16-bit pixels. -/
private theorem readU16BEAt_write_before
    (data : ByteArray) (readBase writeBase : Nat)
    (hread : readBase + 1 < data.size) (hwrite : writeBase + 1 < data.size)
    (x : UInt16) (hbefore : writeBase + 1 < readBase) :
    readU16BEAt (writeU16BEAt data writeBase hwrite x) readBase
      (by simpa [writeU16BEAt_size (data := data) (base := writeBase) (h := hwrite) (x := x)] using hread) =
    readU16BEAt data readBase hread := by
  have hr0 : readBase < data.size := by omega
  have hw0 : writeBase < data.size := by omega
  let data1 := data.set writeBase (u16HighByte x) hw0
  have hsize1 : data1.size = data.size := by
    simpa [data1] using (byteArray_set_size (bs := data) (i := writeBase)
      (hi := hw0) (v := u16HighByte x))
  have hw1 : writeBase + 1 < data1.size := by
    simpa [hsize1] using hwrite
  let data2 := data1.set (writeBase + 1) (u16LowByte x) hw1
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size := by
      simpa [data2] using (byteArray_set_size (bs := data1) (i := writeBase + 1)
        (hi := hw1) (v := u16LowByte x))
    simpa [hsize1] using hsize2'
  have hr0d1 : readBase < data1.size := by simpa [hsize1] using hr0
  have hr1d1 : readBase + 1 < data1.size := by simpa [hsize1] using hread
  have hr0d2 : readBase < data2.size := by simpa [hsize2] using hr0
  have hr1d2 : readBase + 1 < data2.size := by simpa [hsize2] using hread
  have h0keep : data2.get readBase hr0d2 = data.get readBase hr0 := by
    have h2 : data2.get readBase hr0d2 = data1.get readBase hr0d1 := by
      simpa [data2] using
        (byteArray_get_set_ne (bs := data1) (i := writeBase + 1) (j := readBase)
          (hi := hw1) (hj := hr0d1) (hij := by omega) (v := u16LowByte x)
          (h' := hr0d2))
    have h1 : data1.get readBase hr0d1 = data.get readBase hr0 := by
      simpa [data1] using
        (byteArray_get_set_ne (bs := data) (i := writeBase) (j := readBase)
          (hi := hw0) (hj := hr0) (hij := by omega) (v := u16HighByte x)
          (h' := hr0d1))
    simp [h2, h1]
  have h1keep : data2.get (readBase + 1) hr1d2 = data.get (readBase + 1) hread := by
    have h2 : data2.get (readBase + 1) hr1d2 = data1.get (readBase + 1) hr1d1 := by
      simpa [data2] using
        (byteArray_get_set_ne (bs := data1) (i := writeBase + 1) (j := readBase + 1)
          (hi := hw1) (hj := hr1d1) (hij := by omega) (v := u16LowByte x)
          (h' := hr1d2))
    have h1 : data1.get (readBase + 1) hr1d1 = data.get (readBase + 1) hread := by
      simpa [data1] using
        (byteArray_get_set_ne (bs := data) (i := writeBase) (j := readBase + 1)
          (hi := hw0) (hj := hread) (hij := by omega) (v := u16HighByte x)
          (h' := hr1d1))
    simp [h2, h1]
  unfold readU16BEAt writeU16BEAt
  simp [data1, data2, h0keep, h1keep]

def pixelReadRGB8 (data : ByteArray) (base : Nat) (h : base + 2 < data.size) : PixelRGB8 := by
  have h1 : base + 1 < data.size := by omega
  have h0 : base < data.size := by omega
  exact { r := data.get base h0
          g := data.get (base + 1) h1
          b := data.get (base + 2) h }

def pixelWriteRGB8 (data : ByteArray) (base : Nat) (h : base + 2 < data.size)
    (px : PixelRGB8) : ByteArray := by
  have size_set {bs : ByteArray} {i : Nat} (hi : i < bs.size) {v : UInt8} :
      (bs.set i v hi).size = bs.size := by
    cases bs with
    | mk arr =>
        simp [ByteArray.set, ByteArray.size, Array.size_set]
  have h1 : base + 1 < data.size := by omega
  have h0 : base < data.size := by omega
  let data1 := data.set base px.r h0
  have hsize1 : data1.size = data.size := by
    simpa [data1] using (size_set (bs := data) (i := base) (hi := h0) (v := px.r))
  have h1' : base + 1 < data1.size := by
    simpa [hsize1] using h1
  let data2 := data1.set (base + 1) px.g h1'
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size := by
      simpa [data2] using (size_set (bs := data1) (i := base + 1) (hi := h1') (v := px.g))
    simpa [hsize1] using hsize2'
  have h2' : base + 2 < data2.size := by
    simpa [hsize2] using h
  let data3 := data2.set (base + 2) px.b h2'
  exact data3


def pixelReadRGBA8 (data : ByteArray) (base : Nat) (h : base + 3 < data.size) : PixelRGBA8 := by
  have h2 : base + 2 < data.size := by omega
  have h1 : base + 1 < data.size := by omega
  have h0 : base < data.size := by omega
  exact { r := data.get base h0
          g := data.get (base + 1) h1
          b := data.get (base + 2) h2
          a := data.get (base + 3) h }

def pixelWriteRGBA8 (data : ByteArray) (base : Nat) (h : base + 3 < data.size)
    (px : PixelRGBA8) : ByteArray := by
  have size_set {bs : ByteArray} {i : Nat} (hi : i < bs.size) {v : UInt8} :
      (bs.set i v hi).size = bs.size := by
    cases bs with
    | mk arr =>
        simp [ByteArray.set, ByteArray.size, Array.size_set]
  have h2 : base + 2 < data.size := by omega
  have h1 : base + 1 < data.size := by omega
  have h0 : base < data.size := by omega
  let data1 := data.set base px.r h0
  have hsize1 : data1.size = data.size := by
    simpa [data1] using (size_set (bs := data) (i := base) (hi := h0) (v := px.r))
  have h1' : base + 1 < data1.size := by
    simpa [hsize1] using h1
  let data2 := data1.set (base + 1) px.g h1'
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size := by
      simpa [data2] using (size_set (bs := data1) (i := base + 1) (hi := h1') (v := px.g))
    simpa [hsize1] using hsize2'
  have h2' : base + 2 < data2.size := by
    simpa [hsize2] using h2
  let data3 := data2.set (base + 2) px.b h2'
  have hsize3 : data3.size = data.size := by
    have hsize3' : data3.size = data2.size := by
      simpa [data3] using (size_set (bs := data2) (i := base + 2) (hi := h2') (v := px.b))
    simpa [hsize2] using hsize3'
  have h3' : base + 3 < data3.size := by
    simpa [hsize3] using h
  let data4 := data3.set (base + 3) px.a h3'
  exact data4

def pixelReadGray8 (data : ByteArray) (base : Nat) (h : base < data.size) : PixelGray8 := by
  exact { v := data.get base h }

def pixelWriteGray8 (data : ByteArray) (base : Nat) (h : base < data.size)
    (px : PixelGray8) : ByteArray :=
  data.set base px.v h

def pixelReadGrayAlpha8 (data : ByteArray) (base : Nat)
    (h : base + 1 < data.size) : PixelGrayAlpha8 := by
  have h0 : base < data.size := by omega
  exact { v := data.get base h0
          a := data.get (base + 1) h }

def pixelWriteGrayAlpha8 (data : ByteArray) (base : Nat)
    (h : base + 1 < data.size) (px : PixelGrayAlpha8) : ByteArray := by
  have h0 : base < data.size := by omega
  let data1 := data.set base px.v h0
  have hsize1 : data1.size = data.size := by
    cases data with
    | mk arr =>
        simp [data1, ByteArray.set, ByteArray.size, Array.size_set]
  have h1' : base + 1 < data1.size := by
    simpa [hsize1] using h
  exact data1.set (base + 1) px.a h1'

def pixelReadRGB16 (data : ByteArray) (base : Nat)
    (h : base + 5 < data.size) : PixelRGB16 := by
  have hr : base + 1 < data.size := by omega
  have hg : (base + 2) + 1 < data.size := by omega
  have hb : (base + 4) + 1 < data.size := by omega
  exact
    { r := readU16BEAt data base hr
      g := readU16BEAt data (base + 2) hg
      b := readU16BEAt data (base + 4) hb }

def pixelWriteRGB16 (data : ByteArray) (base : Nat)
    (h : base + 5 < data.size) (px : PixelRGB16) : ByteArray := by
  have hr : base + 1 < data.size := by omega
  let data1 := writeU16BEAt data base hr px.r
  have hsize1 : data1.size = data.size := by
    exact writeU16BEAt_size data base hr px.r
  have hg : (base + 2) + 1 < data1.size := by
    simpa [hsize1] using (by omega : (base + 2) + 1 < data.size)
  let data2 := writeU16BEAt data1 (base + 2) hg px.g
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size := by
      exact writeU16BEAt_size data1 (base + 2) hg px.g
    simpa [hsize1] using hsize2'
  have hb : (base + 4) + 1 < data2.size := by
    simpa [hsize2] using (by omega : (base + 4) + 1 < data.size)
  exact writeU16BEAt data2 (base + 4) hb px.b

def pixelReadRGBA16 (data : ByteArray) (base : Nat)
    (h : base + 7 < data.size) : PixelRGBA16 := by
  have hr : base + 1 < data.size := by omega
  have hg : (base + 2) + 1 < data.size := by omega
  have hb : (base + 4) + 1 < data.size := by omega
  have ha : (base + 6) + 1 < data.size := by omega
  exact
    { r := readU16BEAt data base hr
      g := readU16BEAt data (base + 2) hg
      b := readU16BEAt data (base + 4) hb
      a := readU16BEAt data (base + 6) ha }

def pixelWriteRGBA16 (data : ByteArray) (base : Nat)
    (h : base + 7 < data.size) (px : PixelRGBA16) : ByteArray := by
  have hr : base + 1 < data.size := by omega
  let data1 := writeU16BEAt data base hr px.r
  have hsize1 : data1.size = data.size := by
    exact writeU16BEAt_size data base hr px.r
  have hg : (base + 2) + 1 < data1.size := by
    simpa [hsize1] using (by omega : (base + 2) + 1 < data.size)
  let data2 := writeU16BEAt data1 (base + 2) hg px.g
  have hsize2 : data2.size = data.size := by
    have hsize2' : data2.size = data1.size := by
      exact writeU16BEAt_size data1 (base + 2) hg px.g
    simpa [hsize1] using hsize2'
  have hb : (base + 4) + 1 < data2.size := by
    simpa [hsize2] using (by omega : (base + 4) + 1 < data.size)
  let data3 := writeU16BEAt data2 (base + 4) hb px.b
  have hsize3 : data3.size = data.size := by
    have hsize3' : data3.size = data2.size := by
      exact writeU16BEAt_size data2 (base + 4) hb px.b
    simpa [hsize2] using hsize3'
  have ha : (base + 6) + 1 < data3.size := by
    simpa [hsize3] using (by omega : (base + 6) + 1 < data.size)
  exact writeU16BEAt data3 (base + 6) ha px.a

def pixelReadGray16 (data : ByteArray) (base : Nat)
    (h : base + 1 < data.size) : PixelGray16 :=
  { v := readU16BEAt data base h }

def pixelWriteGray16 (data : ByteArray) (base : Nat)
    (h : base + 1 < data.size) (px : PixelGray16) : ByteArray :=
  writeU16BEAt data base h px.v

def pixelReadGrayAlpha16 (data : ByteArray) (base : Nat)
    (h : base + 3 < data.size) : PixelGrayAlpha16 := by
  have hv : base + 1 < data.size := by omega
  have ha : (base + 2) + 1 < data.size := by omega
  exact
    { v := readU16BEAt data base hv
      a := readU16BEAt data (base + 2) ha }

def pixelWriteGrayAlpha16 (data : ByteArray) (base : Nat)
    (h : base + 3 < data.size) (px : PixelGrayAlpha16) : ByteArray := by
  have hv : base + 1 < data.size := by omega
  let data1 := writeU16BEAt data base hv px.v
  have hsize1 : data1.size = data.size := by
    exact writeU16BEAt_size data base hv px.v
  have ha : (base + 2) + 1 < data1.size := by
    simpa [hsize1] using (by omega : (base + 2) + 1 < data.size)
  exact writeU16BEAt data1 (base + 2) ha px.a


structure Bitmap (px : Type u) [Pixel px] where
  mk ::

  size : Size
  data : ByteArray

  valid : data.size = size.width * size.height * Pixel.bytesPerPixel (α := px) := by
    simp
deriving Repr, DecidableEq

abbrev BitmapRGB8 [Pixel PixelRGB8] := Bitmap PixelRGB8
abbrev BitmapRGB16 [Pixel PixelRGB16] := Bitmap PixelRGB16
abbrev BitmapRGBA8 [Pixel PixelRGBA8] := Bitmap PixelRGBA8
abbrev BitmapRGBA16 [Pixel PixelRGBA16] := Bitmap PixelRGBA16
abbrev BitmapGray8 [Pixel PixelGray8] := Bitmap PixelGray8
abbrev BitmapGray16 [Pixel PixelGray16] := Bitmap PixelGray16
abbrev BitmapGrayAlpha8 [Pixel PixelGrayAlpha8] := Bitmap PixelGrayAlpha8
abbrev BitmapGrayAlpha16 [Pixel PixelGrayAlpha16] := Bitmap PixelGrayAlpha16

instance [Pixel PixelRGB8] : DecidableEq BitmapRGB8 := by
  infer_instance

instance [Pixel PixelRGB16] : DecidableEq BitmapRGB16 := by
  infer_instance

instance [Pixel PixelRGBA8] : DecidableEq BitmapRGBA8 := by
  infer_instance

instance [Pixel PixelRGBA16] : DecidableEq BitmapRGBA16 := by
  infer_instance

instance [Pixel PixelGray8] : DecidableEq BitmapGray8 := by
  infer_instance

instance [Pixel PixelGray16] : DecidableEq BitmapGray16 := by
  infer_instance

instance [Pixel PixelGrayAlpha8] : DecidableEq BitmapGrayAlpha8 := by
  infer_instance

instance [Pixel PixelGrayAlpha16] : DecidableEq BitmapGrayAlpha16 := by
  infer_instance

def putPixel {px : Type u} [Pixel px] (img : Bitmap px) (x y : Nat) (pixel : px)
    (h1 : x < img.size.width) (h2: y < img.size.height) : Bitmap px := by
  let pixIdx := x + y * img.size.width
  have hPix : pixIdx < img.size.width * img.size.height := by
    have hx' :
        x + y * img.size.width <
          img.size.width + y * img.size.width := Nat.add_lt_add_right h1 _
    have hx'' :
        x + y * img.size.width <
          img.size.width * (1 + y) := by
      calc
        x + y * img.size.width <
            img.size.width + y * img.size.width := hx'
        _ = img.size.width * (1 + y) := by
            simp [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    have hy' :
        img.size.width * (1 + y) ≤ img.size.width * img.size.height := by
      apply Nat.mul_le_mul_left
      have hyle : y + 1 ≤ img.size.height := Nat.succ_le_of_lt h2
      simpa [Nat.add_comm] using hyle
    have hlt :
        x + y * img.size.width <
          img.size.width * img.size.height := lt_of_lt_of_le hx'' hy'
    simpa [pixIdx] using hlt

  let bpp := Pixel.bytesPerPixel (α := px)
  let base := pixIdx * bpp
  have hlast : base + (bpp - 1) < img.data.size := by
    have hbpp : 0 < bpp := Pixel.bytesPerPixel_pos (α := px)
    have hlt1 : base + (bpp - 1) < base + bpp := by
      have hltbpp : bpp - 1 < bpp := by
        exact Nat.sub_one_lt (Nat.ne_of_gt hbpp)
      exact Nat.add_lt_add_left hltbpp base
    have hle2 : base + bpp ≤ img.size.width * img.size.height * bpp := by
      have hle : pixIdx + 1 ≤ img.size.width * img.size.height := Nat.succ_le_of_lt hPix
      have hle' : (pixIdx + 1) * bpp ≤ img.size.width * img.size.height * bpp :=
        Nat.mul_le_mul_right bpp hle
      have hbase : base + bpp = (pixIdx + 1) * bpp := by
        simp [base, Nat.add_mul, Nat.add_comm]
      simpa [hbase] using hle'
    have hlt : base + (bpp - 1) < img.size.width * img.size.height * bpp :=
      lt_of_lt_of_le hlt1 hle2
    simpa [base, img.valid] using hlt

  let data' := Pixel.write img.data base hlast pixel
  have hsize : data'.size = img.data.size := by
    simpa using Pixel.write_size (data := img.data) (base := base) (h := hlast) (px := pixel)
  exact { img with data := data', valid := by simpa [hsize] using img.valid }

def getPixel {px : Type u} [Pixel px] (img : Bitmap px) (x y : Nat)
    (hx : x < img.size.width)
    (hy : y < img.size.height) : px := by
  let pixIdx := x + y * img.size.width
  have hPix : pixIdx < img.size.width * img.size.height := by
    have hx' :
        x + y * img.size.width <
          img.size.width + y * img.size.width := Nat.add_lt_add_right hx _
    have hx'' :
        x + y * img.size.width <
          img.size.width * (1 + y) := by
      calc
        x + y * img.size.width <
            img.size.width + y * img.size.width := hx'
        _ = img.size.width * (1 + y) := by
            simp [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    have hy' :
        img.size.width * (1 + y) ≤ img.size.width * img.size.height := by
      apply Nat.mul_le_mul_left
      have hyle : y + 1 ≤ img.size.height := Nat.succ_le_of_lt hy
      simpa [Nat.add_comm] using hyle
    have hlt :
        x + y * img.size.width <
          img.size.width * img.size.height := lt_of_lt_of_le hx'' hy'
    simpa [pixIdx] using hlt

  let bpp := Pixel.bytesPerPixel (α := px)
  let base := pixIdx * bpp
  have hlast : base + (bpp - 1) < img.data.size := by
    have hbpp : 0 < bpp := Pixel.bytesPerPixel_pos (α := px)
    have hlt1 : base + (bpp - 1) < base + bpp := by
      have hltbpp : bpp - 1 < bpp := by
        exact Nat.sub_one_lt (Nat.ne_of_gt hbpp)
      exact Nat.add_lt_add_left hltbpp base
    have hle2 : base + bpp ≤ img.size.width * img.size.height * bpp := by
      have hle : pixIdx + 1 ≤ img.size.width * img.size.height := Nat.succ_le_of_lt hPix
      have hle' : (pixIdx + 1) * bpp ≤ img.size.width * img.size.height * bpp :=
        Nat.mul_le_mul_right bpp hle
      have hbase : base + bpp = (pixIdx + 1) * bpp := by
        simp [base, Nat.add_mul, Nat.add_comm]
      simpa [hbase] using hle'
    have hlt : base + (bpp - 1) < img.size.width * img.size.height * bpp :=
      lt_of_lt_of_le hlt1 hle2
    simpa [base, img.valid] using hlt

  exact Pixel.read img.data base hlast

def Bitmap.ofPixelFn {px : Type u} [Pixel px] (w h : Nat) (f : Fin (w * h) → px) : Bitmap px := by
  let bpp := Pixel.bytesPerPixel (α := px)
  let total := w * h * bpp
  let data0 := ByteArray.mk <| Array.replicate total 0
  have hsize0 : data0.size = total := by
    simp [data0, ByteArray.size, Array.size_replicate]
  let rec fill (i : Nat) (data : ByteArray) (hsize : data.size = total) :
      { d : ByteArray // d.size = total } := by
    if hi : i < w * h then
      let base := i * bpp
      have hlast : base + (bpp - 1) < data.size := by
        have hbpp : 0 < bpp := Pixel.bytesPerPixel_pos (α := px)
        have hlt1 : base + (bpp - 1) < base + bpp := by
          have hltbpp : bpp - 1 < bpp := Nat.sub_one_lt (Nat.ne_of_gt hbpp)
          exact Nat.add_lt_add_left hltbpp base
        have hle2 : base + bpp ≤ w * h * bpp := by
          have hle : i + 1 ≤ w * h := Nat.succ_le_of_lt hi
          have hle' : (i + 1) * bpp ≤ w * h * bpp :=
            Nat.mul_le_mul_right bpp hle
          have hbase : base + bpp = (i + 1) * bpp := by
            simp [base, Nat.add_mul, Nat.add_comm]
          simpa [hbase] using hle'
        have hlt : base + (bpp - 1) < w * h * bpp := lt_of_lt_of_le hlt1 hle2
        simpa [hsize] using hlt
      let data' := Pixel.write data base hlast (f ⟨i, hi⟩)
      have hsize' : data'.size = total := by
        simpa [hsize] using
          (Pixel.write_size (data := data) (base := base) (h := hlast) (px := f ⟨i, hi⟩))
      exact fill (i + 1) data' hsize'
    else
      exact ⟨data, hsize⟩
  termination_by w * h - i
  decreasing_by
    have hi' : i < w * h := hi
    have hlt : i < i + 1 := Nat.lt_succ_self i
    exact Nat.sub_lt_sub_left hi' hlt
  let filled := fill 0 data0 hsize0
  refine { size := { width := w, height := h }, data := filled.1, valid := ?_ }
  simpa [total] using filled.2

def mkBlankBitmap (w h : ℕ) (color : PixelRGB8) [Pixel PixelRGB8] : BitmapRGB8 :=
  Bitmap.ofPixelFn w h (fun _ => color)

def BitmapRGB16.ofPixelFn (w h : Nat) (f : Fin (w * h) → PixelRGB16)
    [Pixel PixelRGB16] : BitmapRGB16 :=
  Bitmap.ofPixelFn w h f

def mkBlankBitmapRGB16 (w h : ℕ) (color : PixelRGB16)
    [Pixel PixelRGB16] : BitmapRGB16 :=
  BitmapRGB16.ofPixelFn w h (fun _ => color)

def BitmapRGBA8.ofPixelFn (w h : Nat) (f : Fin (w * h) → PixelRGBA8) [Pixel PixelRGBA8] :
    BitmapRGBA8 :=
  Bitmap.ofPixelFn w h f

def mkBlankBitmapRGBA (w h : ℕ) (color : PixelRGBA8) [Pixel PixelRGBA8] : BitmapRGBA8 :=
  BitmapRGBA8.ofPixelFn w h (fun _ => color)

def BitmapRGBA16.ofPixelFn (w h : Nat) (f : Fin (w * h) → PixelRGBA16)
    [Pixel PixelRGBA16] : BitmapRGBA16 :=
  Bitmap.ofPixelFn w h f

def mkBlankBitmapRGBA16 (w h : ℕ) (color : PixelRGBA16)
    [Pixel PixelRGBA16] : BitmapRGBA16 :=
  BitmapRGBA16.ofPixelFn w h (fun _ => color)

def BitmapGray8.ofPixelFn (w h : Nat) (f : Fin (w * h) → PixelGray8) [Pixel PixelGray8] :
    BitmapGray8 :=
  Bitmap.ofPixelFn w h f

def mkBlankBitmapGray (w h : ℕ) (color : PixelGray8) [Pixel PixelGray8] : BitmapGray8 :=
  BitmapGray8.ofPixelFn w h (fun _ => color)

def BitmapGray16.ofPixelFn (w h : Nat) (f : Fin (w * h) → PixelGray16)
    [Pixel PixelGray16] : BitmapGray16 :=
  Bitmap.ofPixelFn w h f

def mkBlankBitmapGray16 (w h : ℕ) (color : PixelGray16)
    [Pixel PixelGray16] : BitmapGray16 :=
  BitmapGray16.ofPixelFn w h (fun _ => color)

def BitmapGrayAlpha8.ofPixelFn (w h : Nat)
    (f : Fin (w * h) → PixelGrayAlpha8) [Pixel PixelGrayAlpha8] :
    BitmapGrayAlpha8 :=
  Bitmap.ofPixelFn w h f

def mkBlankBitmapGrayAlpha (w h : ℕ) (color : PixelGrayAlpha8)
    [Pixel PixelGrayAlpha8] : BitmapGrayAlpha8 :=
  BitmapGrayAlpha8.ofPixelFn w h (fun _ => color)

def BitmapGrayAlpha16.ofPixelFn (w h : Nat)
    (f : Fin (w * h) → PixelGrayAlpha16) [Pixel PixelGrayAlpha16] :
    BitmapGrayAlpha16 :=
  Bitmap.ofPixelFn w h f

def mkBlankBitmapGrayAlpha16 (w h : ℕ) (color : PixelGrayAlpha16)
    [Pixel PixelGrayAlpha16] : BitmapGrayAlpha16 :=
  BitmapGrayAlpha16.ofPixelFn w h (fun _ => color)

instance instPixelRGB8 : Pixel PixelRGB8 where
  bytesPerPixel := bytesPerPixelRGB
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk r g b =>
        have h2 : base + 2 < data.size := by
          simpa [bytesPerPixelRGB] using h
        have h1 : base + 1 < data.size := by omega
        have h0 : base < data.size := by omega
        have size_set {bs : ByteArray} {i : Nat} (hi : i < bs.size) {v : UInt8} :
            (bs.set i v hi).size = bs.size := by
          cases bs with
          | mk arr =>
              simp [ByteArray.set, ByteArray.size, Array.size_set]
        let data1 := data.set base r h0
        have hsize1 : data1.size = data.size := by
          simp [data1, size_set]
        have h1d1 : base + 1 < data1.size := by
          simpa [hsize1] using h1
        let data2 := data1.set (base + 1) g h1d1
        have hsize2 : data2.size = data.size := by
          have hsize2' : data2.size = data1.size := by
            simp [data2, size_set]
          simpa [hsize1] using hsize2'
        have h2d2 : base + 2 < data2.size := by
          simpa [hsize2] using h2
        let data3 := data2.set (base + 2) b h2d2
        have hsize3 : data3.size = data.size := by
          have hsize3' : data3.size = data2.size := by
            simp [data3, size_set]
          simpa [hsize2] using hsize3'
        have h0d1 : base < data1.size := by
          simpa [hsize1] using h0
        have h0d2 : base < data2.size := by
          simpa [hsize2] using h0
        have h0d3 : base < data3.size := by
          simpa [hsize3] using h0
        have h1d2 : base + 1 < data2.size := by
          simpa [hsize2] using h1
        have h1d3 : base + 1 < data3.size := by
          simpa [hsize3] using h1
        have h2d3 : base + 2 < data3.size := by
          simpa [hsize3] using h2
        have get_set_ne :
            ∀ {bs : ByteArray} {i j : Nat} (hi : i < bs.size) (hj : j < bs.size)
              (hij : i ≠ j) {v : UInt8} {h' : j < (bs.set i v hi).size},
              (bs.set i v hi).get j h' = bs.get j hj := by
          intro bs i j hi hj hij v h'
          cases bs with
          | mk arr =>
              simpa [ByteArray.set, ByteArray.get] using
                (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj)
                  (h := hij))
        have hr : data3.get base h0d3 = r := by
          have hr1 : data3.get base h0d3 = data2.get base h0d2 := by
            simpa [data3] using
              (get_set_ne (bs := data2) (i := base + 2) (j := base)
                (hi := h2d2) (hj := h0d2) (hij := by omega) (v := b) (h' := h0d3))
          have hr2 : data2.get base h0d2 = data1.get base h0d1 := by
            simpa [data2] using
              (get_set_ne (bs := data1) (i := base + 1) (j := base)
                (hi := h1d1) (hj := h0d1) (hij := by omega) (v := g) (h' := h0d2))
          have hr3 : data1.get base h0d1 = r := by
            simp [data1, ByteArray.set, ByteArray.get]
          simp [hr1, hr2, hr3]
        have hg : data3.get (base + 1) h1d3 = g := by
          have hg1 : data3.get (base + 1) h1d3 = data2.get (base + 1) h1d2 := by
            simpa [data3] using
              (get_set_ne (bs := data2) (i := base + 2) (j := base + 1)
                (hi := h2d2) (hj := h1d2) (hij := by omega) (v := b) (h' := h1d3))
          have hg2 : data2.get (base + 1) h1d2 = g := by
            simp [data2, ByteArray.set, ByteArray.get]
          simp [hg1, hg2]
        have hb : data3.get (base + 2) h2d3 = b := by
          simp [data3, ByteArray.set, ByteArray.get]
        simp [pixelReadRGB8, pixelWriteRGB8, data1, data2, data3, hr, hg, hb]
  read := fun data base h =>
    pixelReadRGB8 data base (by simpa [bytesPerPixelRGB] using h)
  write := fun data base h px =>
    pixelWriteRGB8 data base (by simpa [bytesPerPixelRGB] using h) px
  write_size := by
    intro data base h px
    cases data with
    | mk arr =>
        simp [pixelWriteRGB8, ByteArray.set, ByteArray.size, Array.size_set]

instance instPixelRGBA8 : Pixel PixelRGBA8 where
  bytesPerPixel := bytesPerPixelRGBA
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk r g b a =>
        have h3 : base + 3 < data.size := by
          simpa [bytesPerPixelRGBA] using h
        have h2 : base + 2 < data.size := by omega
        have h1 : base + 1 < data.size := by omega
        have h0 : base < data.size := by omega
        have size_set {bs : ByteArray} {i : Nat} (hi : i < bs.size) {v : UInt8} :
            (bs.set i v hi).size = bs.size := by
          cases bs with
          | mk arr =>
              simp [ByteArray.set, ByteArray.size, Array.size_set]
        let data1 := data.set base r h0
        have hsize1 : data1.size = data.size := by
          simp [data1, size_set]
        have h1d1 : base + 1 < data1.size := by
          simpa [hsize1] using h1
        let data2 := data1.set (base + 1) g h1d1
        have hsize2 : data2.size = data.size := by
          have hsize2' : data2.size = data1.size := by
            simp [data2, size_set]
          simpa [hsize1] using hsize2'
        have h2d2 : base + 2 < data2.size := by
          simpa [hsize2] using h2
        let data3 := data2.set (base + 2) b h2d2
        have hsize3 : data3.size = data.size := by
          have hsize3' : data3.size = data2.size := by
            simp [data3, size_set]
          simpa [hsize2] using hsize3'
        have h3d3 : base + 3 < data3.size := by
          simpa [hsize3] using h3
        let data4 := data3.set (base + 3) a h3d3
        have hsize4 : data4.size = data.size := by
          have hsize4' : data4.size = data3.size := by
            simp [data4, size_set]
          simpa [hsize3] using hsize4'
        have h0d1 : base < data1.size := by
          simpa [hsize1] using h0
        have h0d2 : base < data2.size := by
          simpa [hsize2] using h0
        have h0d3 : base < data3.size := by
          simpa [hsize3] using h0
        have h0d4 : base < data4.size := by
          simpa [hsize4] using h0
        have h1d2 : base + 1 < data2.size := by
          simpa [hsize2] using h1
        have h1d3 : base + 1 < data3.size := by
          simpa [hsize3] using h1
        have h1d4 : base + 1 < data4.size := by
          simpa [hsize4] using h1
        have h2d3 : base + 2 < data3.size := by
          simpa [hsize3] using h2
        have h2d4 : base + 2 < data4.size := by
          simpa [hsize4] using h2
        have h3d4 : base + 3 < data4.size := by
          simpa [hsize4] using h3
        have get_set_ne {bs : ByteArray} {i j : Nat}
            (hi : i < bs.size) (hj : j < bs.size) (hij : i ≠ j) {v : UInt8}
            (h' : j < (bs.set i v hi).size) :
            (bs.set i v hi).get j h' = bs.get j hj := by
          cases bs with
          | mk arr =>
              simpa [ByteArray.set, ByteArray.get] using
                (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj)
                  (h := hij))
        have hr : data4.get base h0d4 = r := by
          have hr1 : data4.get base h0d4 = data3.get base h0d3 := by
            simpa [data4] using
              (get_set_ne (bs := data3) (i := base + 3) (j := base)
                (hi := h3d3) (hj := h0d3) (hij := by omega) (v := a) (h' := h0d4))
          have hr2 : data3.get base h0d3 = data2.get base h0d2 := by
            simpa [data3] using
              (get_set_ne (bs := data2) (i := base + 2) (j := base)
                (hi := h2d2) (hj := h0d2) (hij := by omega) (v := b) (h' := h0d3))
          have hr3 : data2.get base h0d2 = data1.get base h0d1 := by
            simpa [data2] using
              (get_set_ne (bs := data1) (i := base + 1) (j := base)
                (hi := h1d1) (hj := h0d1) (hij := by omega) (v := g) (h' := h0d2))
          have hr4 : data1.get base h0d1 = r := by
            simp [data1, ByteArray.set, ByteArray.get]
          simp [hr1, hr2, hr3, hr4]
        have hg : data4.get (base + 1) h1d4 = g := by
          have hg1 : data4.get (base + 1) h1d4 = data3.get (base + 1) h1d3 := by
            simpa [data4] using
              (get_set_ne (bs := data3) (i := base + 3) (j := base + 1)
                (hi := h3d3) (hj := h1d3) (hij := by omega) (v := a) (h' := h1d4))
          have hg2 : data3.get (base + 1) h1d3 = data2.get (base + 1) h1d2 := by
            simpa [data3] using
              (get_set_ne (bs := data2) (i := base + 2) (j := base + 1)
                (hi := h2d2) (hj := h1d2) (hij := by omega) (v := b) (h' := h1d3))
          have hg3 : data2.get (base + 1) h1d2 = g := by
            simp [data2, ByteArray.set, ByteArray.get]
          simp [hg1, hg2, hg3]
        have hb : data4.get (base + 2) h2d4 = b := by
          have hb1 : data4.get (base + 2) h2d4 = data3.get (base + 2) h2d3 := by
            simpa [data4] using
              (get_set_ne (bs := data3) (i := base + 3) (j := base + 2)
                (hi := h3d3) (hj := h2d3) (hij := by omega) (v := a) (h' := h2d4))
          have hb2 : data3.get (base + 2) h2d3 = b := by
            simp [data3, ByteArray.set, ByteArray.get]
          simp [hb1, hb2]
        have ha : data4.get (base + 3) h3d4 = a := by
          simp [data4, ByteArray.set, ByteArray.get]
        simp [pixelReadRGBA8, pixelWriteRGBA8, data1, data2, data3, data4, hr, hg, hb, ha]
  read := fun data base h =>
    pixelReadRGBA8 data base (by simpa [bytesPerPixelRGBA] using h)
  write := fun data base h px =>
    pixelWriteRGBA8 data base (by simpa [bytesPerPixelRGBA] using h) px
  write_size := by
    intro data base h px
    cases data with
    | mk arr =>
        simp [pixelWriteRGBA8, ByteArray.set, ByteArray.size, Array.size_set]

instance instPixelGray8 : Pixel PixelGray8 where
  bytesPerPixel := bytesPerPixelGray
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk v =>
        have h0 : base < data.size := by
          simpa [bytesPerPixelGray] using h
        simp [pixelReadGray8, pixelWriteGray8, ByteArray.set, ByteArray.get]
  read := fun data base h =>
    pixelReadGray8 data base (by simpa [bytesPerPixelGray] using h)
  write := fun data base h px =>
    pixelWriteGray8 data base (by simpa [bytesPerPixelGray] using h) px
  write_size := by
    intro data base h px
    cases data with
    | mk arr =>
        simp [pixelWriteGray8, ByteArray.set, ByteArray.size, Array.size_set]

instance instPixelGrayAlpha8 : Pixel PixelGrayAlpha8 where
  bytesPerPixel := bytesPerPixelGrayAlpha
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk v a =>
        have h1 : base + 1 < data.size := by
          simpa [bytesPerPixelGrayAlpha] using h
        have h0 : base < data.size := by omega
        have size_set {bs : ByteArray} {i : Nat} (hi : i < bs.size) {v : UInt8} :
            (bs.set i v hi).size = bs.size := by
          cases bs with
          | mk arr =>
              simp [ByteArray.set, ByteArray.size, Array.size_set]
        let data1 := data.set base v h0
        have hsize1 : data1.size = data.size := by
          simp [data1, size_set]
        have h1d1 : base + 1 < data1.size := by
          simpa [hsize1] using h1
        let data2 := data1.set (base + 1) a h1d1
        have hsize2 : data2.size = data.size := by
          have hsize2' : data2.size = data1.size := by
            simp [data2, size_set]
          simpa [hsize1] using hsize2'
        have h0d1 : base < data1.size := by
          simpa [hsize1] using h0
        have h0d2 : base < data2.size := by
          simpa [hsize2] using h0
        have h1d2 : base + 1 < data2.size := by
          simpa [hsize2] using h1
        have get_set_ne {bs : ByteArray} {i j : Nat}
            (hi : i < bs.size) (hj : j < bs.size) (hij : i ≠ j) {v : UInt8}
            (h' : j < (bs.set i v hi).size) :
            (bs.set i v hi).get j h' = bs.get j hj := by
          cases bs with
          | mk arr =>
              simpa [ByteArray.set, ByteArray.get] using
                (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj)
                  (h := hij))
        have hv : data2.get base h0d2 = v := by
          have hv1 : data2.get base h0d2 = data1.get base h0d1 := by
            simpa [data2] using
              (get_set_ne (bs := data1) (i := base + 1) (j := base)
                (hi := h1d1) (hj := h0d1) (hij := by omega) (v := a) (h' := h0d2))
          have hv2 : data1.get base h0d1 = v := by
            simp [data1, ByteArray.set, ByteArray.get]
          simp [hv1, hv2]
        have ha : data2.get (base + 1) h1d2 = a := by
          simp [data2, ByteArray.set, ByteArray.get]
        simp [pixelReadGrayAlpha8, pixelWriteGrayAlpha8, data1, data2, hv, ha]
  read := fun data base h =>
    pixelReadGrayAlpha8 data base (by simpa [bytesPerPixelGrayAlpha] using h)
  write := fun data base h px =>
    pixelWriteGrayAlpha8 data base (by simpa [bytesPerPixelGrayAlpha] using h) px
  write_size := by
    intro data base h px
    cases data with
    | mk arr =>
        simp [pixelWriteGrayAlpha8, ByteArray.set, ByteArray.size, Array.size_set]

instance instPixelGray16 : Pixel PixelGray16 where
  bytesPerPixel := bytesPerPixelGray16
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk v =>
        have hv : base + 1 < data.size := by
          simpa [bytesPerPixelGray16] using h
        have hvread := readU16BEAt_write_same data base hv v
        simp [pixelReadGray16, pixelWriteGray16, hvread]
  read := fun data base h =>
    pixelReadGray16 data base (by simpa [bytesPerPixelGray16] using h)
  write := fun data base h px =>
    pixelWriteGray16 data base (by simpa [bytesPerPixelGray16] using h) px
  write_size := by
    intro data base h px
    cases px with
    | mk v =>
        simpa [pixelWriteGray16] using
          (writeU16BEAt_size data base (by simpa [bytesPerPixelGray16] using h) v)

instance instPixelGrayAlpha16 : Pixel PixelGrayAlpha16 where
  bytesPerPixel := bytesPerPixelGrayAlpha16
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk v a =>
        have hv : base + 1 < data.size := by
          have h3 : base + 3 < data.size := by
            simpa [bytesPerPixelGrayAlpha16] using h
          omega
        let data1 := writeU16BEAt data base hv v
        have hsize1 : data1.size = data.size := by
          exact writeU16BEAt_size data base hv v
        have ha : (base + 2) + 1 < data1.size := by
          simpa [hsize1] using
            (by
              have h3 : base + 3 < data.size := by
                simpa [bytesPerPixelGrayAlpha16] using h
              omega : (base + 2) + 1 < data.size)
        let data2 := writeU16BEAt data1 (base + 2) ha a
        have hsize2 : data2.size = data.size := by
          have hsize2' : data2.size = data1.size := by
            exact writeU16BEAt_size data1 (base + 2) ha a
          simpa [hsize1] using hsize2'
        have hv1 : base + 1 < data1.size := by
          simpa [hsize1] using hv
        have hv2 : base + 1 < data2.size := by
          simpa [hsize2] using hv
        have hvr : readU16BEAt data2 base hv2 = v := by
          have hkeep :
              readU16BEAt data2 base hv2 = readU16BEAt data1 base hv1 := by
            simpa [data2] using
              (readU16BEAt_write_after data1 base (base + 2) hv1 ha a (by omega))
          have hsame : readU16BEAt data1 base hv1 = v := by
            simpa [data1] using (readU16BEAt_write_same data base hv v)
          simp [hkeep, hsame]
        have haar : readU16BEAt data2 (base + 2) (by simpa [hsize2, hsize1] using ha) = a := by
          simpa [data2] using (readU16BEAt_write_same data1 (base + 2) ha a)
        simp [pixelReadGrayAlpha16, pixelWriteGrayAlpha16, data1, data2, hvr, haar]
  read := fun data base h =>
    pixelReadGrayAlpha16 data base (by simpa [bytesPerPixelGrayAlpha16] using h)
  write := fun data base h px =>
    pixelWriteGrayAlpha16 data base (by simpa [bytesPerPixelGrayAlpha16] using h) px
  write_size := by
    intro data base h px
    cases px with
    | mk v a =>
        have hv : base + 1 < data.size := by
          have h3 : base + 3 < data.size := by
            simpa [bytesPerPixelGrayAlpha16] using h
          omega
        unfold pixelWriteGrayAlpha16
        simp [writeU16BEAt_size]

instance instPixelRGB16 : Pixel PixelRGB16 where
  bytesPerPixel := bytesPerPixelRGB16
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk r g b =>
        have h5 : base + 5 < data.size := by
          simpa [bytesPerPixelRGB16] using h
        have hr : base + 1 < data.size := by omega
        let data1 := writeU16BEAt data base hr r
        have hsize1 : data1.size = data.size := by
          exact writeU16BEAt_size data base hr r
        have hg : (base + 2) + 1 < data1.size := by
          simpa [hsize1] using (by omega : (base + 2) + 1 < data.size)
        let data2 := writeU16BEAt data1 (base + 2) hg g
        have hsize2 : data2.size = data.size := by
          have hsize2' : data2.size = data1.size := by
            exact writeU16BEAt_size data1 (base + 2) hg g
          simpa [hsize1] using hsize2'
        have hb : (base + 4) + 1 < data2.size := by
          simpa [hsize2] using (by omega : (base + 4) + 1 < data.size)
        let data3 := writeU16BEAt data2 (base + 4) hb b
        have hsize3 : data3.size = data.size := by
          have hsize3' : data3.size = data2.size := by
            exact writeU16BEAt_size data2 (base + 4) hb b
          simpa [hsize2] using hsize3'
        have hr1 : base + 1 < data1.size := by simpa [hsize1] using hr
        have hr2 : base + 1 < data2.size := by simpa [hsize2] using hr
        have hr3 : base + 1 < data3.size := by simpa [hsize3] using hr
        have hg2 : (base + 2) + 1 < data2.size := by simpa [hsize2] using
          (by omega : (base + 2) + 1 < data.size)
        have hg3 : (base + 2) + 1 < data3.size := by simpa [hsize3] using
          (by omega : (base + 2) + 1 < data.size)
        have hb3 : (base + 4) + 1 < data3.size := by simpa [hsize3] using
          (by omega : (base + 4) + 1 < data.size)
        have hrr : readU16BEAt data3 base hr3 = r := by
          have hkeep2 : readU16BEAt data3 base hr3 = readU16BEAt data2 base hr2 := by
            simpa [data3] using
              (readU16BEAt_write_after data2 base (base + 4) hr2 hb b (by omega))
          have hkeep1 : readU16BEAt data2 base hr2 = readU16BEAt data1 base hr1 := by
            simpa [data2] using
              (readU16BEAt_write_after data1 base (base + 2) hr1 hg g (by omega))
          have hsame : readU16BEAt data1 base hr1 = r := by
            simpa [data1] using (readU16BEAt_write_same data base hr r)
          simp [hkeep2, hkeep1, hsame]
        have hgr : readU16BEAt data3 (base + 2) hg3 = g := by
          have hkeep : readU16BEAt data3 (base + 2) hg3 =
              readU16BEAt data2 (base + 2) hg2 := by
            simpa [data3] using
              (readU16BEAt_write_after data2 (base + 2) (base + 4) hg2 hb b
                (by omega))
          have hsame : readU16BEAt data2 (base + 2) hg2 = g := by
            simpa [data2] using (readU16BEAt_write_same data1 (base + 2) hg g)
          simp [hkeep, hsame]
        have hbr : readU16BEAt data3 (base + 4) hb3 = b := by
          simpa [data3] using (readU16BEAt_write_same data2 (base + 4) hb b)
        simp [pixelReadRGB16, pixelWriteRGB16, data1, data2, data3, hrr, hgr, hbr]
  read := fun data base h =>
    pixelReadRGB16 data base (by simpa [bytesPerPixelRGB16] using h)
  write := fun data base h px =>
    pixelWriteRGB16 data base (by simpa [bytesPerPixelRGB16] using h) px
  write_size := by
    intro data base h px
    unfold pixelWriteRGB16
    simp [writeU16BEAt_size]

instance instPixelRGBA16 : Pixel PixelRGBA16 where
  bytesPerPixel := bytesPerPixelRGBA16
  bytesPerPixel_pos := by decide
  read_write := by
    intro data base h px
    cases px with
    | mk r g b a =>
        have h7 : base + 7 < data.size := by
          simpa [bytesPerPixelRGBA16] using h
        have hr : base + 1 < data.size := by omega
        let data1 := writeU16BEAt data base hr r
        have hsize1 : data1.size = data.size := by
          exact writeU16BEAt_size data base hr r
        have hg : (base + 2) + 1 < data1.size := by
          simpa [hsize1] using (by omega : (base + 2) + 1 < data.size)
        let data2 := writeU16BEAt data1 (base + 2) hg g
        have hsize2 : data2.size = data.size := by
          have hsize2' : data2.size = data1.size := by
            exact writeU16BEAt_size data1 (base + 2) hg g
          simpa [hsize1] using hsize2'
        have hb : (base + 4) + 1 < data2.size := by
          simpa [hsize2] using (by omega : (base + 4) + 1 < data.size)
        let data3 := writeU16BEAt data2 (base + 4) hb b
        have hsize3 : data3.size = data.size := by
          have hsize3' : data3.size = data2.size := by
            exact writeU16BEAt_size data2 (base + 4) hb b
          simpa [hsize2] using hsize3'
        have ha : (base + 6) + 1 < data3.size := by
          simpa [hsize3] using (by omega : (base + 6) + 1 < data.size)
        let data4 := writeU16BEAt data3 (base + 6) ha a
        have hsize4 : data4.size = data.size := by
          have hsize4' : data4.size = data3.size := by
            exact writeU16BEAt_size data3 (base + 6) ha a
          simpa [hsize3] using hsize4'
        have hr1 : base + 1 < data1.size := by simpa [hsize1] using hr
        have hr2 : base + 1 < data2.size := by simpa [hsize2] using hr
        have hr3 : base + 1 < data3.size := by simpa [hsize3] using hr
        have hr4 : base + 1 < data4.size := by simpa [hsize4] using hr
        have hg2 : (base + 2) + 1 < data2.size := by simpa [hsize2] using
          (by omega : (base + 2) + 1 < data.size)
        have hg3 : (base + 2) + 1 < data3.size := by simpa [hsize3] using
          (by omega : (base + 2) + 1 < data.size)
        have hg4 : (base + 2) + 1 < data4.size := by simpa [hsize4] using
          (by omega : (base + 2) + 1 < data.size)
        have hb3 : (base + 4) + 1 < data3.size := by simpa [hsize3] using
          (by omega : (base + 4) + 1 < data.size)
        have hb4 : (base + 4) + 1 < data4.size := by simpa [hsize4] using
          (by omega : (base + 4) + 1 < data.size)
        have ha4 : (base + 6) + 1 < data4.size := by simpa [hsize4] using
          (by omega : (base + 6) + 1 < data.size)
        have hrr : readU16BEAt data4 base hr4 = r := by
          have hkeep3 : readU16BEAt data4 base hr4 = readU16BEAt data3 base hr3 := by
            simpa [data4] using
              (readU16BEAt_write_after data3 base (base + 6) hr3 ha a (by omega))
          have hkeep2 : readU16BEAt data3 base hr3 = readU16BEAt data2 base hr2 := by
            simpa [data3] using
              (readU16BEAt_write_after data2 base (base + 4) hr2 hb b (by omega))
          have hkeep1 : readU16BEAt data2 base hr2 = readU16BEAt data1 base hr1 := by
            simpa [data2] using
              (readU16BEAt_write_after data1 base (base + 2) hr1 hg g (by omega))
          have hsame : readU16BEAt data1 base hr1 = r := by
            simpa [data1] using (readU16BEAt_write_same data base hr r)
          simp [hkeep3, hkeep2, hkeep1, hsame]
        have hgr : readU16BEAt data4 (base + 2) hg4 = g := by
          have hkeep3 : readU16BEAt data4 (base + 2) hg4 =
              readU16BEAt data3 (base + 2) hg3 := by
            simpa [data4] using
              (readU16BEAt_write_after data3 (base + 2) (base + 6) hg3 ha a
                (by omega))
          have hkeep2 : readU16BEAt data3 (base + 2) hg3 =
              readU16BEAt data2 (base + 2) hg2 := by
            simpa [data3] using
              (readU16BEAt_write_after data2 (base + 2) (base + 4) hg2 hb b
                (by omega))
          have hsame : readU16BEAt data2 (base + 2) hg2 = g := by
            simpa [data2] using (readU16BEAt_write_same data1 (base + 2) hg g)
          simp [hkeep3, hkeep2, hsame]
        have hbr : readU16BEAt data4 (base + 4) hb4 = b := by
          have hkeep : readU16BEAt data4 (base + 4) hb4 =
              readU16BEAt data3 (base + 4) hb3 := by
            simpa [data4] using
              (readU16BEAt_write_after data3 (base + 4) (base + 6) hb3 ha a
                (by omega))
          have hsame : readU16BEAt data3 (base + 4) hb3 = b := by
            simpa [data3] using (readU16BEAt_write_same data2 (base + 4) hb b)
          simp [hkeep, hsame]
        have har : readU16BEAt data4 (base + 6) ha4 = a := by
          simpa [data4] using (readU16BEAt_write_same data3 (base + 6) ha a)
        simp [pixelReadRGBA16, pixelWriteRGBA16, data1, data2, data3, data4,
          hrr, hgr, hbr, har]
  read := fun data base h =>
    pixelReadRGBA16 data base (by simpa [bytesPerPixelRGBA16] using h)
  write := fun data base h px =>
    pixelWriteRGBA16 data base (by simpa [bytesPerPixelRGBA16] using h) px
  write_size := by
    intro data base h px
    unfold pixelWriteRGBA16
    simp [writeU16BEAt_size]

class FileWritable (α : Type) where
  write : FilePath -> α -> IO (Except String Unit)

class FileReadable (α : Type) where
  read : FilePath -> IO (Except String α)

def ioToExcept {α : Type} (action : IO α) : IO (Except String α) := do
  try
    let v <- action
    return Except.ok v
  catch e =>
    return Except.error (toString e)

end Bitmaps
