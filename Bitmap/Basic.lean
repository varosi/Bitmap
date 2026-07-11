import Bitmap.Compat
import Bitmap.Basic.U16
import Bitmap.Lemmas.BasicU16
import Init.Tactics
import Init.Data.Array.Lemmas
import Init.Data.Array.Set
import Init.Data.ByteArray
import Lean

deriving instance Repr for ByteArray

open Lean
open System (FilePath)

universe u

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

namespace Bitmaps

open Lemmas

structure Size where
  width  : Nat
  height : Nat
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

-------------------------------------------------------------------------------
-- A single color pixel of RGB values of any type
structure RGB (RangeT : Type u) where
  mk ::
  r : RangeT
  g : RangeT
  b : RangeT
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

instance instInhabitedRGB (RangeT) [Inhabited RangeT] : Inhabited (RGB RangeT) where
  default := { r := default, g := default, b := default }

instance instToJsonRGB (RangeT) [ToJson RangeT] : ToJson (RGB RangeT) where
  toJson
    | ⟨r, g, b⟩ =>
      Json.mkObj [
        ("r", toJson r),
        ("g", toJson g),
        ("b", toJson b)
      ]

instance instFromJsonRGB (RangeT) [FromJson RangeT] : FromJson (RGB RangeT) where
  fromJson? j := do
    let r ← j.getObjValAs? RangeT "r"
    let g ← j.getObjValAs? RangeT "g"
    let b ← j.getObjValAs? RangeT "b"
    return { r, g, b }

-- Simple addition of intensities of two pixels
instance {α : Type} [Add α] : Add (RGB α) where
  add p1 p2 := { r := p1.r + p2.r, g := p1.g + p2.g, b := p1.b + p2.b }

instance {α : Type} [Mul α] : Mul (RGB α) where
  mul p1 p2 := { r := p1.r * p2.r, g := p1.g * p2.g, b := p1.b * p2.b }

def RGB8  := RGB UInt8
def RGB16 := RGB UInt16

-------------------------------------------------------------------------------
-- A single color pixel of RGBA values of any type
structure RGBA (RangeT : Type u) where
  mk ::
  r : RangeT
  g : RangeT
  b : RangeT
  a : RangeT
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

instance instInhabitedRGBA (RangeT) [Inhabited RangeT] : Inhabited (RGBA RangeT) where
  default := { r := default, g := default, b := default, a := default }

instance instToJsonRGBA (RangeT) [ToJson RangeT] : ToJson (RGBA RangeT) where
  toJson
    | ⟨r, g, b, a⟩ =>
      Json.mkObj [
        ("r", toJson r),
        ("g", toJson g),
        ("b", toJson b),
        ("a", toJson a)
      ]

instance instFromJsonRGBA (RangeT) [FromJson RangeT] : FromJson (RGBA RangeT) where
  fromJson? j := do
    let r ← j.getObjValAs? RangeT "r"
    let g ← j.getObjValAs? RangeT "g"
    let b ← j.getObjValAs? RangeT "b"
    let a ← j.getObjValAs? RangeT "a"
    return { r, g, b, a }

-- Simple addition of intensities of two pixels
instance (priority := low) {α : Type} [Add α] : Add (RGBA α) where
  add p1 p2 := { r := p1.r + p2.r, g := p1.g + p2.g, b := p1.b + p2.b, a := p1.a + p2.a }

instance (priority := low) {α : Type} [Mul α] : Mul (RGBA α) where
  mul p1 p2 := { r := p1.r * p2.r, g := p1.g * p2.g, b := p1.b * p2.b, a := p1.a * p2.a }

def RGBA8  := RGBA UInt8
def RGBA16 := RGBA UInt16

/-- Byte and numeric operations for one color channel.
It exists so alpha math and pixel byte layouts share one small interface. -/
class ChannelFormat (RangeT : Type u) extends NatCast RangeT where
  toNat : RangeT → Nat
  maxValue : Nat
  byteSize : Nat
  byteSize_pos : 0 < byteSize
  read : (data : ByteArray) → (base : Nat) →
    (h : base + (byteSize - 1) < data.size) → RangeT
  write : (data : ByteArray) → (base : Nat) →
    (h : base + (byteSize - 1) < data.size) → RangeT → ByteArray
  write_size : ∀ (data : ByteArray) (base : Nat)
    (h : base + (byteSize - 1) < data.size) (x : RangeT),
    (write data base h x).size = data.size

instance : ChannelFormat UInt8 where
  natCast := UInt8.ofNat
  toNat := UInt8.toNat
  maxValue := 255
  byteSize := 1
  byteSize_pos := by decide
  read := fun data base h => data.get base (by simpa using h)
  write := fun data base h x => data.set base x (by simpa using h)
  write_size := by
    intro data base h x
    cases data with
    | mk arr =>
        simp [ByteArray.set, ByteArray.size, Array.size_set]

instance : ChannelFormat UInt16 where
  natCast := UInt16.ofNat
  toNat := UInt16.toNat
  maxValue := 65535
  byteSize := 2
  byteSize_pos := by decide
  read := fun data base h => readU16BEAt data base (by simpa using h)
  write := fun data base h x => writeU16BEAt data base (by simpa using h) x
  write_size := by
    intro data base h x
    exact writeU16BEAt_size data base (by simpa using h) x

@[inline] def Alpha.divRound (num den : Nat) : Nat :=
  if den = 0 then
    0
  else
    (num + den / 2) / den

@[inline] def Alpha.clamp {RangeT : Type u} [ChannelFormat RangeT] (n : Nat) : RangeT :=
  Nat.cast (R := RangeT) (Nat.min (ChannelFormat.maxValue (RangeT := RangeT)) n)

@[inline] def Alpha.mulNorm {RangeT : Type u} [ChannelFormat RangeT]
    (x y : RangeT) : RangeT :=
  let max := (ChannelFormat.maxValue (RangeT := RangeT))
  Alpha.clamp (Alpha.divRound (ChannelFormat.toNat x * ChannelFormat.toNat y) max)

@[inline] def Alpha.over {RangeT : Type u} [ChannelFormat RangeT]
    (dstA srcA : RangeT) : RangeT :=
  let src := ChannelFormat.toNat srcA
  let dst := ChannelFormat.toNat dstA
  let max := (ChannelFormat.maxValue (RangeT := RangeT))
  let outA := src + Alpha.divRound (dst * (max - src)) max
  Alpha.clamp outA

@[inline] def Alpha.blendChannelOver {RangeT : Type u} [ChannelFormat RangeT]
    (dstC srcC dstA srcA : RangeT) : RangeT :=
  let src := ChannelFormat.toNat srcA
  let dst := ChannelFormat.toNat dstA
  let max := (ChannelFormat.maxValue (RangeT := RangeT))
  let outA := src + Alpha.divRound (dst * (max - src)) max
  if outA = 0 then
    Alpha.clamp 0
  else
    let srcPremul := ChannelFormat.toNat srcC * src
    let dstPremul := Alpha.divRound (ChannelFormat.toNat dstC * dst * (max - src)) max
    Alpha.clamp (Alpha.divRound ((srcPremul + dstPremul) * max) outA)

-- Alpha compositing: `src` over `dst`.
@[inline] def RGBA.over {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) : RGBA RangeT :=
  let outA := Alpha.over dst.a src.a
  { r := Alpha.blendChannelOver dst.r src.r dst.a src.a
    g := Alpha.blendChannelOver dst.g src.g dst.a src.a
    b := Alpha.blendChannelOver dst.b src.b dst.a src.a
    a := outA }

-- Multiply blend mode composed as `src` over `dst`.
@[inline] def RGBA.multiplyOver {RangeT : Type u} [ChannelFormat RangeT]
    (dst src : RGBA RangeT) : RGBA RangeT :=
  let srcMul : RGBA RangeT :=
    { r := Alpha.mulNorm dst.r src.r
      g := Alpha.mulNorm dst.g src.g
      b := Alpha.mulNorm dst.b src.b
      a := src.a }
  RGBA.over dst srcMul

instance {RangeT : Type u} [ChannelFormat RangeT] : Add (RGBA RangeT) where
  add dst src := RGBA.over dst src

instance {RangeT : Type u} [ChannelFormat RangeT] : Mul (RGBA RangeT) where
  mul dst src := RGBA.multiplyOver dst src

-------------------------------------------------------------------------------
-- A single grayscale pixel of any type
structure Gray (RangeT : Type u) where
  mk ::
  v : RangeT
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

instance instInhabitedGray (RangeT) [Inhabited RangeT] : Inhabited (Gray RangeT) where
  default := { v := default }

instance instToJsonGray (RangeT) [ToJson RangeT] : ToJson (Gray RangeT) where
  toJson
    | ⟨v⟩ =>
      Json.mkObj [
        ("v", toJson v)
      ]

instance instFromJsonGray (RangeT) [FromJson RangeT] : FromJson (Gray RangeT) where
  fromJson? j := do
    let v ← j.getObjValAs? RangeT "v"
    return { v }

instance {α : Type} [Add α] : Add (Gray α) where
  add p1 p2 := { v := p1.v + p2.v }

instance {α : Type} [Mul α] : Mul (Gray α) where
  mul p1 p2 := { v := p1.v * p2.v }

def Gray8 := Gray UInt8
def Gray16 := Gray UInt16

-------------------------------------------------------------------------------
-- A packed one-bit grayscale pixel.
structure Gray1 where
  mk ::
  v : Bool
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

instance : Inhabited Gray1 where
  default := { v := false }

instance : ToJson Gray1 where
  toJson
    | ⟨v⟩ =>
      Json.mkObj [
        ("v", toJson v)
      ]

instance : FromJson Gray1 where
  fromJson? j := do
    let v ← j.getObjValAs? Bool "v"
    return { v }

-------------------------------------------------------------------------------
-- A single grayscale pixel with alpha of any type
structure GrayAlpha (RangeT : Type u) where
  mk ::
  v : RangeT
  a : RangeT
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

instance instInhabitedGrayAlpha (RangeT) [Inhabited RangeT] :
    Inhabited (GrayAlpha RangeT) where
  default := { v := default, a := default }

instance instToJsonGrayAlpha (RangeT) [ToJson RangeT] :
    ToJson (GrayAlpha RangeT) where
  toJson
    | ⟨v, a⟩ =>
      Json.mkObj [
        ("v", toJson v),
        ("a", toJson a)
      ]

instance instFromJsonGrayAlpha (RangeT) [FromJson RangeT] :
    FromJson (GrayAlpha RangeT) where
  fromJson? j := do
    let v ← j.getObjValAs? RangeT "v"
    let a ← j.getObjValAs? RangeT "a"
    return { v, a }

instance {α : Type} [Add α] : Add (GrayAlpha α) where
  add p1 p2 := { v := p1.v + p2.v, a := p1.a + p2.a }

instance {α : Type} [Mul α] : Mul (GrayAlpha α) where
  mul p1 p2 := { v := p1.v * p2.v, a := p1.a * p2.a }

def GrayAlpha8 := GrayAlpha UInt8
def GrayAlpha16 := GrayAlpha UInt16

instance : Inhabited RGB8 := instInhabitedRGB _
instance : DecidableEq RGB8 := by
  unfold RGB8
  infer_instance

instance : Inhabited RGB16 := instInhabitedRGB _
instance : DecidableEq RGB16 := by
  unfold RGB16
  infer_instance

instance : Inhabited RGBA8 := instInhabitedRGBA _
instance : DecidableEq RGBA8 := by
  unfold RGBA8
  infer_instance

instance : Inhabited RGBA16 := instInhabitedRGBA _
instance : DecidableEq RGBA16 := by
  unfold RGBA16
  infer_instance

instance : Inhabited Gray8 := instInhabitedGray _
instance : DecidableEq Gray8 := by
  unfold Gray8
  infer_instance

instance : Inhabited Gray16 := instInhabitedGray _
instance : DecidableEq Gray16 := by
  unfold Gray16
  infer_instance

instance : Inhabited GrayAlpha8 := instInhabitedGrayAlpha _
instance : DecidableEq GrayAlpha8 := by
  unfold GrayAlpha8
  infer_instance

instance : Inhabited GrayAlpha16 := instInhabitedGrayAlpha _
instance : DecidableEq GrayAlpha16 := by
  unfold GrayAlpha16
  infer_instance

-------------------------------------------------------------------------------
-- Format metadata for byte layout.
class PixelFormat (α : Type u) where
  bytesPerPixel : Nat
  bytesPerPixel_pos : 0 < bytesPerPixel
  read : (data : ByteArray) -> (base : Nat) ->
    (h : base + (bytesPerPixel - 1) < data.size) -> α
  write : (data : ByteArray) -> (base : Nat) ->
    (h : base + (bytesPerPixel - 1) < data.size) -> α -> ByteArray
  write_size : ∀ (data : ByteArray) (base : Nat)
    (h : base + (bytesPerPixel - 1) < data.size) (px : α),
    (write data base h px).size = data.size

def RGB8.bytesPerPixel : Nat := 3
def RGBA8.bytesPerPixel : Nat := 4
def Gray8.bytesPerPixel : Nat := 1
def GrayAlpha8.bytesPerPixel : Nat := 2
def RGB16.bytesPerPixel : Nat := 6
def RGBA16.bytesPerPixel : Nat := 8
def Gray16.bytesPerPixel : Nat := 2
def GrayAlpha16.bytesPerPixel : Nat := 4

def gray1RowBytes (w : Nat) : Nat :=
  (w + 7) / 8

def gray1DataSize (w h : Nat) : Nat :=
  h * gray1RowBytes w

@[inline] def gray1BitMask (x : Nat) : UInt8 :=
  UInt8.ofNat (1 <<< (7 - (x % 8)))

@[inline] def gray1BitClearMask (x : Nat) : UInt8 :=
  UInt8.ofNat (255 - (gray1BitMask x).toNat)

@[inline] def gray1BitIsSet (byte : UInt8) (x : Nat) : Bool :=
  (byte &&& gray1BitMask x) != 0

@[inline] def gray1SetBitInByte (byte : UInt8) (x : Nat) (bit : Bool) : UInt8 :=
  if bit then
    byte ||| gray1BitMask x
  else
    byte &&& gray1BitClearMask x

@[inline] def gray1ByteIndex (w x y : Nat) : Nat :=
  y * gray1RowBytes w + x / 8

@[inline] def gray1FullByte (px : Gray1) : UInt8 :=
  if px.v then 0xff else 0

namespace ChannelLayout

theorem bound2_0 {RangeT : Type u} [ChannelFormat RangeT]
    {data : ByteArray} {base : Nat}
    (h : base + (2 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) :
    base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
  have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
  omega

theorem bound2_1 {RangeT : Type u} [ChannelFormat RangeT]
    {data : ByteArray} {base : Nat}
    (h : base + (2 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) :
    base + ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
  have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
  omega

theorem bound3_0 {RangeT : Type u} [ChannelFormat RangeT]
    {data : ByteArray} {base : Nat}
    (h : base + (3 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) :
    base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
  have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
  omega

theorem bound3_1 {RangeT : Type u} [ChannelFormat RangeT]
    {data : ByteArray} {base : Nat}
    (h : base + (3 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) :
    base + ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
  have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
  omega

theorem bound3_2 {RangeT : Type u} [ChannelFormat RangeT]
    {data : ByteArray} {base : Nat}
    (h : base + (3 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) :
    base + 2 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
  have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
  omega

theorem bound4_0 {RangeT : Type u} [ChannelFormat RangeT]
    {data : ByteArray} {base : Nat}
    (h : base + (4 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) :
    base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
  have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
  omega

theorem bound4_1 {RangeT : Type u} [ChannelFormat RangeT]
    {data : ByteArray} {base : Nat}
    (h : base + (4 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) :
    base + ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
  have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
  omega

theorem bound4_2 {RangeT : Type u} [ChannelFormat RangeT]
    {data : ByteArray} {base : Nat}
    (h : base + (4 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) :
    base + 2 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
  have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
  omega

theorem bound4_3 {RangeT : Type u} [ChannelFormat RangeT]
    {data : ByteArray} {base : Nat}
    (h : base + (4 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) :
    base + 3 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
  have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
  omega

@[inline] def read1 {RangeT α : Type u} [ChannelFormat RangeT]
    (mk : RangeT → α) (data : ByteArray) (base : Nat)
    (h : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) : α :=
  mk (ChannelFormat.read data base h)

@[inline] def write1 {RangeT α : Type u} [ChannelFormat RangeT]
    (get0 : α → RangeT) (data : ByteArray) (base : Nat)
    (h : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) : ByteArray :=
  ChannelFormat.write data base h (get0 px)

theorem write1_size {RangeT α : Type u} [ChannelFormat RangeT]
    (get0 : α → RangeT) (data : ByteArray) (base : Nat)
    (h : base + (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) :
    (write1 get0 data base h px).size = data.size := by
  unfold write1
  exact ChannelFormat.write_size data base h (get0 px)

@[inline] def read2 {RangeT α : Type u} [ChannelFormat RangeT]
    (mk : RangeT → RangeT → α) (data : ByteArray) (base : Nat)
    (h : base + (2 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) : α :=
  mk
    (ChannelFormat.read data base (bound2_0 h))
    (ChannelFormat.read data (base + ChannelFormat.byteSize (RangeT := RangeT)) (bound2_1 h))

@[inline] def write2 {RangeT α : Type u} [ChannelFormat RangeT]
    (get0 get1 : α → RangeT) (data : ByteArray) (base : Nat)
    (h : base + (2 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) : ByteArray :=
  let h0 := bound2_0 h
  let data1 := ChannelFormat.write data base h0 (get0 px)
  have hsize1 : data1.size = data.size :=
    ChannelFormat.write_size data base h0 (get0 px)
  let h1 : base + ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data1.size := by
    simpa [hsize1] using bound2_1 h
  ChannelFormat.write data1 (base + ChannelFormat.byteSize (RangeT := RangeT)) h1 (get1 px)

theorem write2_size {RangeT α : Type u} [ChannelFormat RangeT]
    (get0 get1 : α → RangeT) (data : ByteArray) (base : Nat)
    (h : base + (2 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) :
    (write2 get0 get1 data base h px).size = data.size := by
  unfold write2
  simp [ChannelFormat.write_size]

@[inline] def read3 {RangeT α : Type u} [ChannelFormat RangeT]
    (mk : RangeT → RangeT → RangeT → α) (data : ByteArray) (base : Nat)
    (h : base + (3 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) : α :=
  mk
    (ChannelFormat.read data base (bound3_0 h))
    (ChannelFormat.read data (base + ChannelFormat.byteSize (RangeT := RangeT)) (bound3_1 h))
    (ChannelFormat.read data (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) (bound3_2 h))

@[inline] def write3 {RangeT α : Type u} [ChannelFormat RangeT]
    (get0 get1 get2 : α → RangeT) (data : ByteArray) (base : Nat)
    (h : base + (3 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) : ByteArray :=
  let h01 : base + (2 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
    have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
    omega
  let data2 := write2 get0 get1 data base h01 px
  have hsize2 : data2.size = data.size :=
    write2_size get0 get1 data base h01 px
  let h2 : base + 2 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data2.size := by
    simpa [hsize2] using bound3_2 h
  ChannelFormat.write data2 (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) h2 (get2 px)

theorem write3_size {RangeT α : Type u} [ChannelFormat RangeT]
    (get0 get1 get2 : α → RangeT) (data : ByteArray) (base : Nat)
    (h : base + (3 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) :
    (write3 get0 get1 get2 data base h px).size = data.size := by
  unfold write3
  simp [write2_size, ChannelFormat.write_size]

@[inline] def read4 {RangeT α : Type u} [ChannelFormat RangeT]
    (mk : RangeT → RangeT → RangeT → RangeT → α) (data : ByteArray) (base : Nat)
    (h : base + (4 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size) : α :=
  mk
    (ChannelFormat.read data base (bound4_0 h))
    (ChannelFormat.read data (base + ChannelFormat.byteSize (RangeT := RangeT)) (bound4_1 h))
    (ChannelFormat.read data (base + 2 * ChannelFormat.byteSize (RangeT := RangeT)) (bound4_2 h))
    (ChannelFormat.read data (base + 3 * ChannelFormat.byteSize (RangeT := RangeT)) (bound4_3 h))

@[inline] def write4 {RangeT α : Type u} [ChannelFormat RangeT]
    (get0 get1 get2 get3 : α → RangeT) (data : ByteArray) (base : Nat)
    (h : base + (4 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) : ByteArray :=
  let h012 : base + (3 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size := by
    have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
    omega
  let data3 := write3 get0 get1 get2 data base h012 px
  have hsize3 : data3.size = data.size :=
    write3_size get0 get1 get2 data base h012 px
  let h3 : base + 3 * ChannelFormat.byteSize (RangeT := RangeT) +
      (ChannelFormat.byteSize (RangeT := RangeT) - 1) < data3.size := by
    simpa [hsize3] using bound4_3 h
  ChannelFormat.write data3 (base + 3 * ChannelFormat.byteSize (RangeT := RangeT)) h3 (get3 px)

theorem write4_size {RangeT α : Type u} [ChannelFormat RangeT]
    (get0 get1 get2 get3 : α → RangeT) (data : ByteArray) (base : Nat)
    (h : base + (4 * ChannelFormat.byteSize (RangeT := RangeT) - 1) < data.size)
    (px : α) :
    (write4 get0 get1 get2 get3 data base h px).size = data.size := by
  unfold write4
  simp [write3_size, ChannelFormat.write_size]

@[reducible] def pixelFormat1 {RangeT α : Type u} [ChannelFormat RangeT]
    (mk : RangeT → α) (get0 : α → RangeT) : PixelFormat α where
  bytesPerPixel := ChannelFormat.byteSize (RangeT := RangeT)
  bytesPerPixel_pos := ChannelFormat.byteSize_pos (RangeT := RangeT)
  read := read1 mk
  write := write1 get0
  write_size := write1_size get0

@[reducible] def pixelFormat2 {RangeT α : Type u} [ChannelFormat RangeT]
    (mk : RangeT → RangeT → α) (get0 get1 : α → RangeT) : PixelFormat α where
  bytesPerPixel := 2 * ChannelFormat.byteSize (RangeT := RangeT)
  bytesPerPixel_pos := by
    have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
    omega
  read := read2 mk
  write := write2 get0 get1
  write_size := write2_size get0 get1

@[reducible] def pixelFormat3 {RangeT α : Type u} [ChannelFormat RangeT]
    (mk : RangeT → RangeT → RangeT → α) (get0 get1 get2 : α → RangeT) : PixelFormat α where
  bytesPerPixel := 3 * ChannelFormat.byteSize (RangeT := RangeT)
  bytesPerPixel_pos := by
    have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
    omega
  read := read3 mk
  write := write3 get0 get1 get2
  write_size := write3_size get0 get1 get2

@[reducible] def pixelFormat4 {RangeT α : Type u} [ChannelFormat RangeT]
    (mk : RangeT → RangeT → RangeT → RangeT → α) (get0 get1 get2 get3 : α → RangeT) :
    PixelFormat α where
  bytesPerPixel := 4 * ChannelFormat.byteSize (RangeT := RangeT)
  bytesPerPixel_pos := by
    have hpos := ChannelFormat.byteSize_pos (RangeT := RangeT)
    omega
  read := read4 mk
  write := write4 get0 get1 get2 get3
  write_size := write4_size get0 get1 get2 get3

end ChannelLayout

structure Bitmap (px : Type u) [PixelFormat px] where
  mk ::

  size : Size
  data : ByteArray

  valid : data.size = size.width * size.height * PixelFormat.bytesPerPixel (α := px) := by
    simp
deriving Repr, DecidableEq

structure Bitmap.Gray1 where
  mk ::

  size : Size
  data : ByteArray

  valid : data.size = gray1DataSize size.width size.height := by
    simp [gray1DataSize]
deriving Repr, DecidableEq

abbrev Bitmap.RGB8 [inst : PixelFormat Bitmaps.RGB8] := @Bitmap Bitmaps.RGB8 inst
abbrev Bitmap.RGB16 [inst : PixelFormat Bitmaps.RGB16] := @Bitmap Bitmaps.RGB16 inst
abbrev Bitmap.RGBA8 [inst : PixelFormat Bitmaps.RGBA8] := @Bitmap Bitmaps.RGBA8 inst
abbrev Bitmap.RGBA16 [inst : PixelFormat Bitmaps.RGBA16] := @Bitmap Bitmaps.RGBA16 inst
abbrev Bitmap.Gray8 [inst : PixelFormat Bitmaps.Gray8] := @Bitmap Bitmaps.Gray8 inst
abbrev Bitmap.Gray16 [inst : PixelFormat Bitmaps.Gray16] := @Bitmap Bitmaps.Gray16 inst
abbrev Bitmap.GrayAlpha8 [inst : PixelFormat Bitmaps.GrayAlpha8] := @Bitmap Bitmaps.GrayAlpha8 inst
abbrev Bitmap.GrayAlpha16 [inst : PixelFormat Bitmaps.GrayAlpha16] := @Bitmap Bitmaps.GrayAlpha16 inst

instance [PixelFormat Bitmaps.RGB8] : DecidableEq Bitmap.RGB8 := by
  infer_instance

instance [PixelFormat Bitmaps.RGB16] : DecidableEq Bitmap.RGB16 := by
  infer_instance

instance [PixelFormat Bitmaps.RGBA8] : DecidableEq Bitmap.RGBA8 := by
  infer_instance

instance [PixelFormat Bitmaps.RGBA16] : DecidableEq Bitmap.RGBA16 := by
  infer_instance

instance [PixelFormat Bitmaps.Gray8] : DecidableEq Bitmap.Gray8 := by
  infer_instance

instance [PixelFormat Bitmaps.Gray16] : DecidableEq Bitmap.Gray16 := by
  infer_instance

instance [PixelFormat Bitmaps.GrayAlpha8] : DecidableEq Bitmap.GrayAlpha8 := by
  infer_instance

instance [PixelFormat Bitmaps.GrayAlpha16] : DecidableEq Bitmap.GrayAlpha16 := by
  infer_instance

def Bitmap.setPixel {px : Type u} [PixelFormat px] (img : Bitmap px) (x y : Nat) (pixel : px)
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

  let bpp := PixelFormat.bytesPerPixel (α := px)
  let base := pixIdx * bpp
  have hlast : base + (bpp - 1) < img.data.size := by
    have hbpp : 0 < bpp := PixelFormat.bytesPerPixel_pos (α := px)
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

  let data' := PixelFormat.write img.data base hlast pixel
  have hsize : data'.size = img.data.size := by
    simpa using PixelFormat.write_size (data := img.data) (base := base) (h := hlast) (px := pixel)
  exact { img with data := data', valid := by simpa [hsize] using img.valid }

def Bitmap.getPixel {px : Type u} [PixelFormat px] (img : Bitmap px) (x y : Nat)
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

  let bpp := PixelFormat.bytesPerPixel (α := px)
  let base := pixIdx * bpp
  have hlast : base + (bpp - 1) < img.data.size := by
    have hbpp : 0 < bpp := PixelFormat.bytesPerPixel_pos (α := px)
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

  exact PixelFormat.read img.data base hlast

def Bitmap.ofFn {px : Type u} [PixelFormat px] (w h : Nat) (f : Fin (w * h) → px) : Bitmap px := by
  let bpp := PixelFormat.bytesPerPixel (α := px)
  let total := w * h * bpp
  let data0 := ByteArray.mk <| Array.replicate total 0
  have hsize0 : data0.size = total := by
    simp [data0, ByteArray.size, Array.size_replicate]
  let rec fill (i : Nat) (data : ByteArray) (hsize : data.size = total) :
      { d : ByteArray // d.size = total } := by
    if hi : i < w * h then
      let base := i * bpp
      have hlast : base + (bpp - 1) < data.size := by
        have hbpp : 0 < bpp := PixelFormat.bytesPerPixel_pos (α := px)
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
      let data' := PixelFormat.write data base hlast (f ⟨i, hi⟩)
      have hsize' : data'.size = total := by
        simpa [hsize] using
          (PixelFormat.write_size (data := data) (base := base) (h := hlast) (px := f ⟨i, hi⟩))
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

def Bitmap.fill {px : Type u} [PixelFormat px] (w h : Nat) (color : px) : Bitmap px :=
  Bitmap.ofFn w h (fun _ => color)

def Bitmap.RGB8.ofFn (w h : Nat) (f : Fin (w * h) → Bitmaps.RGB8)
    [PixelFormat Bitmaps.RGB8] : Bitmap.RGB8 :=
  Bitmap.ofFn w h f

def Bitmap.RGB16.ofFn (w h : Nat) (f : Fin (w * h) → Bitmaps.RGB16)
    [PixelFormat Bitmaps.RGB16] : Bitmap.RGB16 :=
  Bitmap.ofFn w h f

def Bitmap.RGBA8.ofFn (w h : Nat) (f : Fin (w * h) → Bitmaps.RGBA8)
    [PixelFormat Bitmaps.RGBA8] :
    Bitmap.RGBA8 :=
  Bitmap.ofFn w h f

def Bitmap.RGBA16.ofFn (w h : Nat) (f : Fin (w * h) → Bitmaps.RGBA16)
    [PixelFormat Bitmaps.RGBA16] : Bitmap.RGBA16 :=
  Bitmap.ofFn w h f

def Bitmap.Gray8.ofFn (w h : Nat) (f : Fin (w * h) → Bitmaps.Gray8)
    [PixelFormat Bitmaps.Gray8] :
    Bitmap.Gray8 :=
  Bitmap.ofFn w h f

def Bitmap.Gray16.ofFn (w h : Nat) (f : Fin (w * h) → Bitmaps.Gray16)
    [PixelFormat Bitmaps.Gray16] : Bitmap.Gray16 :=
  Bitmap.ofFn w h f

def Bitmap.GrayAlpha8.ofFn (w h : Nat)
    (f : Fin (w * h) → Bitmaps.GrayAlpha8) [PixelFormat Bitmaps.GrayAlpha8] :
    Bitmap.GrayAlpha8 :=
  Bitmap.ofFn w h f

def Bitmap.GrayAlpha16.ofFn (w h : Nat)
    (f : Fin (w * h) → Bitmaps.GrayAlpha16) [PixelFormat Bitmaps.GrayAlpha16] :
    Bitmap.GrayAlpha16 :=
  Bitmap.ofFn w h f

private def gray1PackedByteOfFn (w h rowBytes : Nat)
    (i : Fin (h * rowBytes)) (f : Fin (w * h) → Bitmaps.Gray1) : UInt8 :=
  Id.run do
    let y := i.val / rowBytes
    let byteX := i.val % rowBytes
    let mut byte : UInt8 := 0
    if hy : y < h then
      for bit in [0:8] do
        let x := byteX * 8 + bit
        if hx : x < w then
          let pixIdx := x + y * w
          have hpix : pixIdx < w * h := by
            have hx' : x + y * w < w + y * w := Nat.add_lt_add_right hx _
            have hx'' : x + y * w < w * (y + 1) := by
              simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
                Nat.mul_comm] using hx'
            have hy' : w * (y + 1) ≤ w * h :=
              Nat.mul_le_mul_left w (Nat.succ_le_of_lt hy)
            exact lt_of_lt_of_le hx'' hy'
          if (f ⟨pixIdx, hpix⟩).v then
            byte := gray1SetBitInByte byte x true
    return byte

def Bitmap.Gray1.ofFn (w h : Nat) (f : Fin (w * h) → Bitmaps.Gray1) :
    Bitmap.Gray1 :=
  let rowBytes := gray1RowBytes w
  let data := ByteArray.mk <|
    Array.ofFn (fun i : Fin (h * rowBytes) => gray1PackedByteOfFn w h rowBytes i f)
  { size := { width := w, height := h }
    data := data
    valid := by
      change (Array.ofFn
        (fun i : Fin (h * rowBytes) => gray1PackedByteOfFn w h rowBytes i f)).size =
          gray1DataSize w h
      simp [gray1DataSize, rowBytes] }

def Bitmap.Gray1.fill (w h : Nat) (color : Bitmaps.Gray1) : Bitmap.Gray1 :=
  Bitmap.Gray1.ofFn w h (fun _ => color)

def Bitmap.Gray1.getBitLinear (bmp : Bitmap.Gray1) (i : Nat) : Bool :=
  if _hpix : i < bmp.size.width * bmp.size.height then
    if bmp.size.width == 0 then
      false
    else
      let x := i % bmp.size.width
      let y := i / bmp.size.width
      let byte := bmp.data.get! (gray1ByteIndex bmp.size.width x y)
      gray1BitIsSet byte x
  else
    false

def Bitmap.Gray1.getPixel? (bmp : Bitmap.Gray1) (x y : Nat) : Option Bitmaps.Gray1 :=
  if _hx : x < bmp.size.width then
    if _hy : y < bmp.size.height then
      let byte := bmp.data.get! (gray1ByteIndex bmp.size.width x y)
      some { v := gray1BitIsSet byte x }
    else
      none
  else
    none

def Bitmap.Gray1.setPixel? (bmp : Bitmap.Gray1) (x y : Nat) (px : Bitmaps.Gray1) :
    Option Bitmap.Gray1 :=
  if _hx : x < bmp.size.width then
    if _hy : y < bmp.size.height then
      let idx := gray1ByteIndex bmp.size.width x y
      if hidx : idx < bmp.data.size then
        let byte := bmp.data.get idx hidx
        let data := bmp.data.set idx (gray1SetBitInByte byte x px.v) hidx
        have hdataSize : data.size = bmp.data.size := by
          cases hdata : bmp.data with
          | mk arr =>
              simp only [data, hdata, ByteArray.set, ByteArray.size, Array.size_set]
        some
          { size := bmp.size
            data := data
            valid := by
              calc
                data.size = bmp.data.size := hdataSize
                _ = gray1DataSize bmp.size.width bmp.size.height := bmp.valid }
      else
        none
    else
      none
  else
    none

def Bitmap.Gray1.toGray8 (bmp : Bitmap.Gray1) [PixelFormat Bitmaps.Gray8] : Bitmap.Gray8 :=
  Bitmap.Gray8.ofFn bmp.size.width bmp.size.height (fun idx =>
    { v := if bmp.getBitLinear idx.val then 0xff else 0 })

def Bitmap.Gray1.toRGB8 (bmp : Bitmap.Gray1) [PixelFormat Bitmaps.RGB8] : Bitmap.RGB8 :=
  Bitmap.ofFn bmp.size.width bmp.size.height (fun idx =>
    let v : UInt8 := if bmp.getBitLinear idx.val then 0xff else 0
    { r := v, g := v, b := v })

def Bitmap.Gray1.toRGBA8 (bmp : Bitmap.Gray1) [PixelFormat Bitmaps.RGBA8] : Bitmap.RGBA8 :=
  Bitmap.RGBA8.ofFn bmp.size.width bmp.size.height (fun idx =>
    let v : UInt8 := if bmp.getBitLinear idx.val then 0xff else 0
    { r := v, g := v, b := v, a := 0xff })

def Bitmap.Gray8.toGray1Threshold [PixelFormat Bitmaps.Gray8] (bmp : Bitmap.Gray8)
    (threshold : UInt8 := 128) :
    Bitmap.Gray1 :=
  Bitmap.Gray1.ofFn bmp.size.width bmp.size.height (fun idx =>
    { v := (bmp.data.get! idx.val).toNat >= threshold.toNat })

instance instPixelFormatRGB8 : PixelFormat RGB8 :=
  ChannelLayout.pixelFormat3
    (fun r g b => { r := r, g := g, b := b })
    RGB.r RGB.g RGB.b

instance instPixelFormatRGBA8 : PixelFormat RGBA8 :=
  ChannelLayout.pixelFormat4
    (fun r g b a => { r := r, g := g, b := b, a := a })
    RGBA.r RGBA.g RGBA.b RGBA.a

instance instPixelFormatGray8 : PixelFormat Gray8 :=
  ChannelLayout.pixelFormat1
    (fun v => { v := v })
    Gray.v

instance instPixelFormatGrayAlpha8 : PixelFormat GrayAlpha8 :=
  ChannelLayout.pixelFormat2
    (fun v a => { v := v, a := a })
    GrayAlpha.v GrayAlpha.a

instance instPixelFormatGray16 : PixelFormat Gray16 :=
  ChannelLayout.pixelFormat1
    (fun v => { v := v })
    Gray.v

instance instPixelFormatGrayAlpha16 : PixelFormat GrayAlpha16 :=
  ChannelLayout.pixelFormat2
    (fun v a => { v := v, a := a })
    GrayAlpha.v GrayAlpha.a

instance instPixelFormatRGB16 : PixelFormat RGB16 :=
  ChannelLayout.pixelFormat3
    (fun r g b => { r := r, g := g, b := b })
    RGB.r RGB.g RGB.b

instance instPixelFormatRGBA16 : PixelFormat RGBA16 :=
  ChannelLayout.pixelFormat4
    (fun r g b a => { r := r, g := g, b := b, a := a })
    RGBA.r RGBA.g RGBA.b RGBA.a

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
