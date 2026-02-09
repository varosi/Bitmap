import Mathlib.Data.Nat.Basic
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
instance {α : Type} [Add α] : Add (PixelRGBA α) where
  add p1 p2 := { r := p1.r + p2.r, g := p1.g + p2.g, b := p1.b + p2.b, a := p1.a + p2.a }

instance {α : Type} [Mul α] : Mul (PixelRGBA α) where
  mul p1 p2 := { r := p1.r * p2.r, g := p1.g * p2.g, b := p1.b * p2.b, a := p1.a * p2.a }

def PixelRGBA8  := PixelRGBA UInt8

instance : Inhabited PixelRGB8 := instInhabitedPixelRGB _
instance : DecidableEq PixelRGB8 := by
  unfold PixelRGB8
  infer_instance

instance : Inhabited PixelRGBA8 := instInhabitedPixelRGBA _
instance : DecidableEq PixelRGBA8 := by
  unfold PixelRGBA8
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
          simpa [data1] using (size_set (bs := data) (i := base) (hi := h0) (v := r))
        have h1d1 : base + 1 < data1.size := by
          simpa [hsize1] using h1
        let data2 := data1.set (base + 1) g h1d1
        have hsize2 : data2.size = data.size := by
          have hsize2' : data2.size = data1.size := by
            simpa [data2] using (size_set (bs := data1) (i := base + 1) (hi := h1d1) (v := g))
          simpa [hsize1] using hsize2'
        have h2d2 : base + 2 < data2.size := by
          simpa [hsize2] using h2
        let data3 := data2.set (base + 2) b h2d2
        have hsize3 : data3.size = data.size := by
          have hsize3' : data3.size = data2.size := by
            simpa [data3] using (size_set (bs := data2) (i := base + 2) (hi := h2d2) (v := b))
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
                (Array.getElem_set_ne (xs := arr) (i := i) (j := j) (h' := hi) (pj := hj) (h := hij))
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
          simpa [data1] using (size_set (bs := data) (i := base) (hi := h0) (v := r))
        have h1d1 : base + 1 < data1.size := by
          simpa [hsize1] using h1
        let data2 := data1.set (base + 1) g h1d1
        have hsize2 : data2.size = data.size := by
          have hsize2' : data2.size = data1.size := by
            simpa [data2] using
              (size_set (bs := data1) (i := base + 1) (hi := h1d1) (v := g))
          simpa [hsize1] using hsize2'
        have h2d2 : base + 2 < data2.size := by
          simpa [hsize2] using h2
        let data3 := data2.set (base + 2) b h2d2
        have hsize3 : data3.size = data.size := by
          have hsize3' : data3.size = data2.size := by
            simpa [data3] using
              (size_set (bs := data2) (i := base + 2) (hi := h2d2) (v := b))
          simpa [hsize2] using hsize3'
        have h3d3 : base + 3 < data3.size := by
          simpa [hsize3] using h3
        let data4 := data3.set (base + 3) a h3d3
        have hsize4 : data4.size = data.size := by
          have hsize4' : data4.size = data3.size := by
            simpa [data4] using
              (size_set (bs := data3) (i := base + 3) (hi := h3d3) (v := a))
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

structure Bitmap (px : Type u) [Pixel px] where
  mk ::

  size : Size
  data : ByteArray

  valid : data.size = size.width * size.height * Pixel.bytesPerPixel (α := px) := by
    simp
deriving Repr, DecidableEq

abbrev BitmapRGB8 := Bitmap PixelRGB8
abbrev BitmapRGBA8 := Bitmap PixelRGBA8

instance : DecidableEq BitmapRGB8 := by
  infer_instance

instance : DecidableEq BitmapRGBA8 := by
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

def Bitmap.ofPixelFn (w h : Nat) (f : Fin (w * h) → PixelRGB8) : BitmapRGB8 := by
  refine
    { size := { width := w, height := h }
      data := ByteArray.mk <| Array.ofFn (fun i : Fin (w * h * bytesPerPixelRGB) =>
        let pixIdx := i.val / bytesPerPixelRGB
        have hidx : pixIdx < w * h := by
          have hlt : i.val < bytesPerPixelRGB * (w * h) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using i.isLt
          exact Nat.div_lt_of_lt_mul hlt
        let px := f ⟨pixIdx, hidx⟩
        match i.val % bytesPerPixelRGB with
        | 0 => px.r
        | 1 => px.g
        | _ => px.b)
      valid := ?_ }
  have hbpp : Pixel.bytesPerPixel (α := PixelRGB8) = bytesPerPixelRGB := by
    rfl
  simp [bytesPerPixelRGB, hbpp, ByteArray.size, Array.size_ofFn, Nat.mul_assoc]

def mkBlankBitmap (w h : ℕ) (color : PixelRGB8) : BitmapRGB8 :=
  Bitmap.ofPixelFn w h (fun _ => color)

def BitmapRGBA8.ofPixelFn (w h : Nat) (f : Fin (w * h) → PixelRGBA8) : BitmapRGBA8 := by
  refine
    { size := { width := w, height := h }
      data := ByteArray.mk <| Array.ofFn (fun i : Fin (w * h * bytesPerPixelRGBA) =>
        let pixIdx := i.val / bytesPerPixelRGBA
        have hidx : pixIdx < w * h := by
          have hlt : i.val < bytesPerPixelRGBA * (w * h) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using i.isLt
          exact Nat.div_lt_of_lt_mul hlt
        let px := f ⟨pixIdx, hidx⟩
        match i.val % bytesPerPixelRGBA with
        | 0 => px.r
        | 1 => px.g
        | 2 => px.b
        | _ => px.a)
      valid := ?_ }
  have hbpp : Pixel.bytesPerPixel (α := PixelRGBA8) = bytesPerPixelRGBA := by
    rfl
  simp [bytesPerPixelRGBA, hbpp, ByteArray.size, Array.size_ofFn, Nat.mul_assoc]

def mkBlankBitmapRGBA (w h : ℕ) (color : PixelRGBA8) : BitmapRGBA8 :=
  BitmapRGBA8.ofPixelFn w h (fun _ => color)

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

-------------------------------------------------------------------------------
-- PNG read/write for BitmapRGB8

namespace Png

def u8 (n : Nat) : UInt8 :=
  UInt8.ofNat n

def u16le (n : Nat) : ByteArray :=
  ByteArray.mk #[u8 (n % 256), u8 ((n / 256) % 256)]

def u32be (n : Nat) : ByteArray :=
  ByteArray.mk #[
    u8 ((n / 2 ^ 24) % 256),
    u8 ((n / 2 ^ 16) % 256),
    u8 ((n / 2 ^ 8) % 256),
    u8 (n % 256)
  ]

def readU16LE (bytes : ByteArray) (pos : Nat) (h : pos + 1 < bytes.size) : Nat :=
  let b0 := bytes.get pos (by omega)
  let b1 := bytes.get (pos + 1) (by simpa using h)
  b0.toNat + (b1.toNat <<< 8)

def readU32BE (bytes : ByteArray) (pos : Nat) (h : pos + 3 < bytes.size) : Nat :=
  let b0 := bytes.get pos (by omega)
  let b1 := bytes.get (pos + 1) (by omega)
  let b2 := bytes.get (pos + 2) (by omega)
  let b3 := bytes.get (pos + 3) (by omega)
  (b0.toNat <<< 24) + (b1.toNat <<< 16) + (b2.toNat <<< 8) + b3.toNat

def crc32Table : Array UInt32 :=
  Id.run do
    let mut table : Array UInt32 := Array.mkEmpty 256
    for i in [0:256] do
      let mut c : UInt32 := UInt32.ofNat i
      for _ in [0:8] do
        if (c &&& 1) == (1 : UInt32) then
          c := (0xEDB88320 : UInt32) ^^^ (c >>> 1)
        else
          c := c >>> 1
      table := table.push c
    return table

def crc32 (bytes : ByteArray) : UInt32 :=
  Id.run do
    let mut c : UInt32 := 0xFFFFFFFF
    for b in bytes do
      let idx : Nat := ((c ^^^ (UInt32.ofNat b.toNat)) &&& (0xFF : UInt32)).toNat
      c := crc32Table[idx]! ^^^ (c >>> 8)
    return c ^^^ 0xFFFFFFFF

def adler32 (bytes : ByteArray) : UInt32 :=
  Id.run do
    let mod : Nat := 65521
    let mut a : Nat := 1
    let mut b : Nat := 0
    for byte in bytes do
      a := (a + byte.toNat) % mod
      b := (b + a) % mod
    return UInt32.ofNat ((b <<< 16) + a)

def pngSignature : ByteArray :=
  ByteArray.mk #[
    u8 0x89, u8 0x50, u8 0x4E, u8 0x47,
    u8 0x0D, u8 0x0A, u8 0x1A, u8 0x0A
  ]

def mkChunk (typ : String) (data : ByteArray) : ByteArray :=
  let typBytes := typ.toUTF8
  let lenBytes := u32be data.size
  let crc := crc32 (typBytes ++ data)
  lenBytes ++ typBytes ++ data ++ u32be crc.toNat

def storedBlock (payload : ByteArray) (final : Bool) : ByteArray :=
  let len := payload.size
  ByteArray.mk #[if final then u8 0x01 else u8 0x00]
    ++ u16le len ++ u16le (0xFFFF - len) ++ payload

def deflateStored (raw : ByteArray) : ByteArray :=
  if _hzero : raw.size = 0 then
    storedBlock ByteArray.empty true
  else
    let blockLen := if raw.size > 65535 then 65535 else raw.size
    let final := blockLen == raw.size
    let payload := raw.extract 0 blockLen
    let block := storedBlock payload final
    if _hfinal : final then
      block
    else
      block ++ deflateStored (raw.extract blockLen raw.size)
termination_by raw.size
decreasing_by
  have hle : blockLen ≤ raw.size := by
    by_cases hlarge : raw.size > 65535
    · have : (65535 : Nat) ≤ raw.size := Nat.le_of_lt hlarge
      simpa [blockLen, hlarge] using this
    · simp [blockLen, hlarge]
  have hpos : 0 < blockLen := by
    have hpos_raw : 0 < raw.size := Nat.pos_of_ne_zero _hzero
    by_cases hlarge : raw.size > 65535
    · simp [blockLen, hlarge]
    · simp [blockLen, hlarge, hpos_raw]
  simp [ByteArray.size_extract]
  exact Nat.sub_lt_self hpos hle

def zlibCompressStored (raw : ByteArray) : ByteArray :=
  let header := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateStored raw
  let adler := u32be (adler32 raw).toNat
  header ++ deflated ++ adler

structure BitReader where
  data : ByteArray
  bytePos : Nat
  bitPos : Nat
  hpos : bytePos ≤ data.size
  hend : bytePos = data.size → bitPos = 0
  hbit : bitPos < 8
deriving Repr

def BitReader.bitIndex (br : BitReader) : Nat :=
  br.bytePos * 8 + br.bitPos

def BitReader.readBit (br : BitReader) : Nat × BitReader :=
  if hEq : br.bytePos = br.data.size then
    (0, br)
  else
    let hlt : br.bytePos < br.data.size := lt_of_le_of_ne br.hpos hEq
    let byte := br.data.get br.bytePos hlt
    let bitNat := (byte.toNat >>> br.bitPos) &&& 1
    let nextBitPos := br.bitPos + 1
    if hnext : nextBitPos = 8 then
      let hpos' : br.bytePos + 1 ≤ br.data.size := Nat.succ_le_of_lt hlt
      (bitNat,
        { data := br.data
          bytePos := br.bytePos + 1
          bitPos := 0
          hpos := hpos'
          hend := by intro _; rfl
          hbit := by decide })
    else
      let hend' : br.bytePos = br.data.size → nextBitPos = 0 := by
        intro hEq'
        exact (False.elim (hEq hEq'))
      have hbit' : nextBitPos < 8 := by
        have hle : nextBitPos <= 8 := Nat.succ_le_of_lt br.hbit
        exact lt_of_le_of_ne hle hnext
      (bitNat,
        { data := br.data
          bytePos := br.bytePos
          bitPos := nextBitPos
          hpos := br.hpos
          hend := hend'
          hbit := hbit' })

def BitReader.readBits (br : BitReader) (n : Nat)
    (h : br.bitIndex + n <= br.data.size * 8) : Nat × BitReader := by
  induction n generalizing br with
  | zero =>
      exact (0, br)
  | succ n ih =>
      have hlt : br.bitIndex < br.data.size * 8 := by
        have hpos : 0 < Nat.succ n := Nat.succ_pos _
        have hlt' : br.bitIndex < br.bitIndex + Nat.succ n :=
          Nat.lt_add_of_pos_right (n := br.bitIndex) (k := Nat.succ n) hpos
        exact lt_of_lt_of_le hlt' h
      have hle : br.bytePos * 8 <= br.bitIndex := by
        dsimp [BitReader.bitIndex]
        exact Nat.le_add_right _ _
      have hmul : br.bytePos * 8 < br.data.size * 8 := lt_of_le_of_lt hle hlt
      have hbyte : br.bytePos < br.data.size := by
        have hmul' : 8 * br.bytePos < 8 * br.data.size := by
          simpa [Nat.mul_comm] using hmul
        exact Nat.lt_of_mul_lt_mul_left hmul'
      cases hres : br.readBit with
      | mk bit br' =>
          have hindex' : (BitReader.readBit br).2.bitIndex = br.bitIndex + 1 := by
            unfold BitReader.readBit BitReader.bitIndex
            have hne : br.bytePos ≠ br.data.size := ne_of_lt hbyte
            by_cases hnext : br.bitPos + 1 = 8
            · calc
                (BitReader.readBit br).2.bitIndex
                    = (br.bytePos + 1) * 8 := by
                        simp [BitReader.readBit, BitReader.bitIndex, hne, hnext]
                _ = br.bytePos * 8 + (br.bitPos + 1) := by
                        simp [Nat.add_mul, hnext, Nat.add_comm]
                _ = br.bitIndex + 1 := by
                        simp [BitReader.bitIndex, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            · simp [hne, hnext, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have hdata' : (br.readBit).2.data = br.data := by
            unfold BitReader.readBit
            have hne : br.bytePos ≠ br.data.size := ne_of_lt hbyte
            by_cases hnext : br.bitPos + 1 = 8 <;> simp [hne, hnext]
          have hindex : br'.bitIndex = br.bitIndex + 1 := by
            simpa [hres] using hindex'
          have hdata : br'.data = br.data := by
            simpa [hres] using hdata'
          have h' : br'.bitIndex + n <= br'.data.size * 8 := by
            have h'raw : br'.bitIndex + n <= br.data.size * 8 := by
              simpa [hindex, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
            simpa [hdata] using h'raw
          let (rest, br'') := ih br' h'
          exact (bit ||| (rest <<< 1), br'')

def BitReader.alignByte (br : BitReader) : BitReader :=
  by
    by_cases hzero : br.bitPos = 0
    · exact br
    ·
      have hne : br.bytePos ≠ br.data.size := by
        intro hEq
        have hbit0 : br.bitPos = 0 := br.hend hEq
        exact hzero hbit0
      have hlt : br.bytePos < br.data.size := lt_of_le_of_ne br.hpos hne
      have hpos' : br.bytePos + 1 ≤ br.data.size := Nat.succ_le_of_lt hlt
      exact
        { data := br.data
          bytePos := br.bytePos + 1
          bitPos := 0
          hpos := hpos'
          hend := by intro _; rfl
          hbit := by decide }

structure Huffman where
  maxLen : Nat
  table : Array (Array (Option Nat))
deriving Repr

def reverseBits (code len : Nat) : Nat :=
  Id.run do
    let mut x := code
    let mut res := 0
    for _ in [0:len] do
      let bit := x &&& 1
      res := (res <<< 1) ||| bit
      x := x >>> 1
    return res

def mkHuffman (lengths : Array Nat) : Option Huffman := do
  let mut maxLen := 0
  for l in lengths do
    if l > maxLen then
      maxLen := l
  if maxLen == 0 then
    none
  let mut count : Array Nat := Array.replicate (maxLen + 1) 0
  for l in lengths do
    if l > 0 then
      count := count.set! l (count[l]! + 1)
  let mut nextCode : Array Nat := Array.replicate (maxLen + 1) 0
  let mut code := 0
  for bits in [1:maxLen + 1] do
    code := (code + count[bits - 1]!) <<< 1
    nextCode := nextCode.set! bits code
  let mut table : Array (Array (Option Nat)) := Array.mkEmpty (maxLen + 1)
  table := table.push (#[])
  for bits in [1:maxLen + 1] do
    table := table.push (Array.replicate (1 <<< bits) none)
  for idx in [0:lengths.size] do
    let len := lengths[idx]!
    if len > 0 then
      let codeVal := nextCode[len]!
      nextCode := nextCode.set! len (codeVal + 1)
      let rev := reverseBits codeVal len
      let row := table[len]!
      if rev >= row.size then
        none
      let row' := row.set! rev (some idx)
      table := table.set! len row'
  return { maxLen, table }

partial def Huffman.decode (h : Huffman) (br : BitReader) : Option (Nat × BitReader) := do
  let mut code := 0
  let mut len := 0
  let mut br := br
  while len < h.maxLen do
    if br.bytePos < br.data.size then
      let (bit, br') := br.readBit
      br := br'
      code := code ||| (bit <<< len)
      len := len + 1
    else
      none
    if hlen : h.table.size <= len then
      pure ()
    else
      let row := Array.getInternal h.table len (Nat.lt_of_not_ge hlen)
      if hcode : code < row.size then
        match Array.getInternal row code hcode with
        | some sym => return (sym, br)
        | none => pure ()
      else
        pure ()
  none

def lengthBases : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10,
    11, 13, 15, 17,
    19, 23, 27, 31,
    35, 43, 51, 59,
    67, 83, 99, 115,
    131, 163, 195, 227,
    258]

def lengthExtra : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1,
    2, 2, 2, 2,
    3, 3, 3, 3,
    4, 4, 4, 4,
    5, 5, 5, 5,
    0]

def distBases : Array Nat :=
  #[1, 2, 3, 4,
    5, 7,
    9, 13,
    17, 25,
    33, 49,
    65, 97,
    129, 193,
    257, 385,
    513, 769,
    1025, 1537,
    2049, 3073,
    4097, 6145,
    8193, 12289,
    16385, 24577]

def distExtra : Array Nat :=
  #[0, 0, 0, 0,
    1, 1,
    2, 2,
    3, 3,
    4, 4,
    5, 5,
    6, 6,
    7, 7,
    8, 8,
    9, 9,
    10, 10,
    11, 11,
    12, 12,
    13, 13]

def decodeLength (sym : Nat) (br : BitReader)
    (h : 257 ≤ sym ∧ sym ≤ 285)
    (hbits : br.bitIndex + (lengthExtra[(sym - 257)]'
      (by
        have hidxlt : sym - 257 < 29 := by omega
        have hsize : lengthExtra.size = 29 := by decide
        simpa [hsize] using hidxlt)) <= br.data.size * 8) :
    Nat × BitReader :=
  let idx := sym - 257
  have hidxle : idx ≤ 28 := by
    dsimp [idx]
    omega
  have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
  have hLengthBasesSize : lengthBases.size = 29 := by decide
  have hLengthExtraSize : lengthExtra.size = 29 := by decide
  have hidxBase : idx < lengthBases.size := by simpa [hLengthBasesSize] using hidxlt
  have hidxExtra : idx < lengthExtra.size := by simpa [hLengthExtraSize] using hidxlt
  let base := Array.getInternal lengthBases idx hidxBase
  let extra := Array.getInternal lengthExtra idx hidxExtra
  if hextra : extra = 0 then
    (base, br)
  else
    let (bits, br') := br.readBits extra (by simpa [hextra] using hbits)
    (base + bits, br')

def decodeDistance (sym : Nat) (br : BitReader)
    (h : sym < distBases.size)
    (hbits : br.bitIndex + distExtra[sym]'
      (by
        have hDistExtraSize : distExtra.size = 30 := by decide
        have hDistBasesSize : distBases.size = 30 := by decide
        simpa [hDistExtraSize, hDistBasesSize] using h) <= br.data.size * 8) :
    Nat × BitReader :=
  have hDistExtraSize : distExtra.size = 30 := by decide
  have hDistBasesSize : distBases.size = 30 := by decide
  have hdistExtra : sym < distExtra.size := by
    simpa [hDistExtraSize, hDistBasesSize] using h
  let base := Array.getInternal distBases sym h
  let extra := Array.getInternal distExtra sym hdistExtra
  if hextra : extra = 0 then
    (base, br)
  else
    let (bits, br') := br.readBits extra (by simpa [hextra] using hbits)
    (base + bits, br')

partial def decodeCompressedBlock (litLen dist : Huffman) (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) := do
  let mut br := br
  let mut out := out
  let hLengthExtraSize : lengthExtra.size = 29 := by decide
  let hDistBasesSize : distBases.size = 30 := by decide
  let hDistExtraSize : distExtra.size = 30 := by decide
  while true do
    let (sym, br') ← litLen.decode br
    br := br'
    if sym < 256 then
      out := out.push (u8 sym)
    else if sym == 256 then
      return (br, out)
    if hlen : 257 ≤ sym ∧ sym ≤ 285 then
      let idx := sym - 257
      have hidxle : idx ≤ 28 := by
        dsimp [idx]
        omega
      have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
      have hidxExtra : idx < lengthExtra.size := by simpa [hLengthExtraSize] using hidxlt
      let extra := Array.getInternal lengthExtra idx hidxExtra
      if hbits : br.bitIndex + extra <= br.data.size * 8 then
        let (len, br'') := decodeLength sym br hlen (by simpa using hbits)
        br := br''
        let (distSym, br''') ← dist.decode br
        br := br'''
        if hdist : distSym < distBases.size then
          let extraD := Array.getInternal distExtra distSym (by
            simpa [hDistExtraSize, hDistBasesSize] using hdist)
          if hbitsD : br.bitIndex + extraD <= br.data.size * 8 then
            let (distance, br'''') := decodeDistance distSym br hdist (by simpa using hbitsD)
            br := br''''
            if distance == 0 || distance > out.size then
              none
            let mut i := 0
            while i < len do
              let idx := out.size - distance
              let b := out.get! idx
              out := out.push b
              i := i + 1
          else
            none
        else
          none
      else
        none
    else
      none
  return (br, out)

partial def readDynamicTables (br : BitReader) : Option (Huffman × Huffman × BitReader) := do
  let (hlitBits, br) ←
    if h : br.bitIndex + 5 <= br.data.size * 8 then
      some (br.readBits 5 h)
    else
      none
  let (hdistBits, br) ←
    if h : br.bitIndex + 5 <= br.data.size * 8 then
      some (br.readBits 5 h)
    else
      none
  let (hclenBits, br) ←
    if h : br.bitIndex + 4 <= br.data.size * 8 then
      some (br.readBits 4 h)
    else
      none
  let hlit := hlitBits + 257
  let hdist := hdistBits + 1
  let hclen := hclenBits + 4
  let order : Array Nat := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
  let mut codeLenLengths : Array Nat := Array.replicate 19 0
  let mut br := br
  for i in [0:hclen] do
    let (len, br') ←
      if h : br.bitIndex + 3 <= br.data.size * 8 then
        some (br.readBits 3 h)
      else
        none
    codeLenLengths := codeLenLengths.set! order[i]! len
    br := br'
  let codeLenTable ← mkHuffman codeLenLengths
  let total := hlit + hdist
  let mut lengths : Array Nat := Array.mkEmpty total
  while lengths.size < total do
    let (sym, br') ← codeLenTable.decode br
    br := br'
    if sym <= 15 then
      lengths := lengths.push sym
    else if sym == 16 then
      if lengths.size == 0 then
        none
      let (extra, br'') ←
        if h : br.bitIndex + 2 <= br.data.size * 8 then
          some (br.readBits 2 h)
        else
          none
      br := br''
      let repeatCount := 3 + extra
      let prev := lengths[lengths.size - 1]!
      for _ in [0:repeatCount] do
        lengths := lengths.push prev
    else if sym == 17 then
      let (extra, br'') ←
        if h : br.bitIndex + 3 <= br.data.size * 8 then
          some (br.readBits 3 h)
        else
          none
      br := br''
      let repeatCount := 3 + extra
      for _ in [0:repeatCount] do
        lengths := lengths.push 0
    else if sym == 18 then
      let (extra, br'') ←
        if h : br.bitIndex + 7 <= br.data.size * 8 then
          some (br.readBits 7 h)
        else
          none
      br := br''
      let repeatCount := 11 + extra
      for _ in [0:repeatCount] do
        lengths := lengths.push 0
    else
      none
  if lengths.size != total then
    none
  let litLenLengths := lengths.extract 0 hlit
  let distLengths := lengths.extract hlit (hlit + hdist)
  let litLenTable ← mkHuffman litLenLengths
  let distTable ← mkHuffman distLengths
  return (litLenTable, distTable, br)

def fixedLitLenLengths : Array Nat :=
  Id.run do
    let mut arr : Array Nat := Array.replicate 288 0
    for i in [0:144] do
      arr := arr.set! i 8
    for i in [144:256] do
      arr := arr.set! i 9
    for i in [256:280] do
      arr := arr.set! i 7
    for i in [280:288] do
      arr := arr.set! i 8
    return arr

partial def zlibDecompress (data : ByteArray) (hsize : 2 <= data.size) : Option ByteArray := do
  let h0 : 0 < data.size := by omega
  let h1 : 1 < data.size := by omega
  let cmf := data.get 0 h0
  let flg := data.get 1 h1
  if ((cmf.toNat <<< 8) + flg.toNat) % 31 != 0 then
    none
  if (cmf &&& (0x0F : UInt8)) != (8 : UInt8) then
    none
  if (flg &&& (0x20 : UInt8)) != (0 : UInt8) then
    none
  let mut br : BitReader := {
    data := data
    bytePos := 2
    bitPos := 0
    hpos := hsize
    hend := by intro _; rfl
    hbit := by decide
  }
  let mut out := ByteArray.empty
  let mut final := false
  while not final do
    let (bfinal, br1) ←
      if h : br.bitIndex + 1 <= br.data.size * 8 then
        some (br.readBits 1 h)
      else
        none
    let (btype, br2) ←
      if h : br1.bitIndex + 2 <= br1.data.size * 8 then
        some (br1.readBits 2 h)
      else
        none
    br := br2
    final := bfinal == 1
    if btype == 0 then
      br := br.alignByte
      if h : br.bytePos + 3 < data.size then
        let len := readU16LE data br.bytePos (by omega)
        let nlen := readU16LE data (br.bytePos + 2) (by omega)
        if len + nlen != 0xFFFF then
          none
        let start := br.bytePos + 4
        if hlen : start + len > data.size then
          none
        else
          out := out ++ data.extract start (start + len)
          have hle : start + len ≤ data.size := Nat.le_of_not_gt hlen
          br := {
            data := data
            bytePos := start + len
            bitPos := 0
            hpos := hle
            hend := by intro _; rfl
            hbit := by decide
          }
      else
        none
    else if btype == 1 then
      let litLenTable ← mkHuffman fixedLitLenLengths
      let distTable ← mkHuffman (Array.replicate 32 5)
      let (br', out') ← decodeCompressedBlock litLenTable distTable br out
      br := br'
      out := out'
    else if btype == 2 then
      let (litLenTable, distTable, br') ← readDynamicTables br
      let (br'', out') ← decodeCompressedBlock litLenTable distTable br' out
      br := br''
      out := out'
    else
      none
  let brAligned := br.alignByte
  if hAdler : brAligned.bytePos + 3 < data.size then
    let adlerExpected := readU32BE data brAligned.bytePos hAdler
    let adlerActual := (adler32 out).toNat
    if adlerExpected != adlerActual then
      none
  else
    none
  return out

-- Parse stored (uncompressed) deflate blocks from a deflated byte stream.
-- Returns the decoded payload and any remaining suffix.
def inflateStoredAux (data : ByteArray) (h : 0 < data.size) : Option (ByteArray × ByteArray) := do
  let header := data.get 0 h
  let bfinal := header &&& (0x01 : UInt8)
  let btype := (header >>> 1) &&& (0x03 : UInt8)
  if btype != (0 : UInt8) then
    none
  if hlen : 1 + 3 < data.size then
    let len := readU16LE data 1 (by omega)
    let nlen := readU16LE data 3 (by omega)
    if len + nlen != 0xFFFF then
      none
    let start := 5
    if hbad : start + len > data.size then
      none
    else
      let payload := data.extract start (start + len)
      let next := data.extract (start + len) data.size
      if bfinal == (1 : UInt8) then
        return (payload, next)
      else
        if hnext : start + len < data.size then
          have hnextsize : next.size = data.size - (start + len) := by
            simp [next, ByteArray.size_extract]
          have hnext' : 0 < next.size := by
            have hpos : 0 < data.size - (start + len) := Nat.sub_pos_of_lt hnext
            simpa [hnextsize] using hpos
          let (tail, rest) ← inflateStoredAux next hnext'
          return (payload ++ tail, rest)
        else
          none
  else
    none
termination_by data.size
decreasing_by
  -- The recursive call consumes at least the 5-byte header.
  have hle : 5 + readU16LE data 1 (by omega) ≤ data.size := by
    exact not_lt.mp hbad
  have hpos : 0 < 5 + readU16LE data 1 (by omega) := by omega
  -- Reduce the suffix size and apply `Nat.sub_lt_self`.
  simp [ByteArray.size_extract]
  exact Nat.sub_lt_self hpos hle

-- Inflate stored blocks and require the stream to end exactly at the final block.
partial def inflateStored (data : ByteArray) : Option ByteArray := do
  if h : 0 < data.size then
    let (payload, rest) ← inflateStoredAux data h
    if rest.size == 0 then
      return payload
    else
      none
  else
    none

-- Fast path for zlib streams that use only stored (uncompressed) deflate blocks.
partial def zlibDecompressStored (data : ByteArray) (hsize : 2 <= data.size) : Option ByteArray := do
  let cmf := data.get 0 (by omega)
  let flg := data.get 1 (by omega)
  if ((cmf.toNat <<< 8) + flg.toNat) % 31 != 0 then
    none
  if (cmf &&& (0x0F : UInt8)) != (8 : UInt8) then
    none
  if (flg &&& (0x20 : UInt8)) != (0 : UInt8) then
    none
  if hmin : 6 ≤ data.size then
    let deflated := data.extract 2 (data.size - 4)
    let out ← inflateStored deflated
    let pos := data.size - 4
    have hAdler : pos + 3 < data.size := by
      have : 4 ≤ data.size := by omega
      omega
    let adlerExpected := readU32BE data pos hAdler
    let adlerActual := (adler32 out).toNat
    if adlerExpected != adlerActual then
      none
    return out
  else
    none

structure PngHeader where
  width : Nat
  height : Nat
  colorType : Nat
  bitDepth : Nat
deriving Repr

def readChunk (bytes : ByteArray) (pos : Nat)
    (hLen : pos + 3 < bytes.size) :
    Option (ByteArray × ByteArray × Nat) :=
  let len := readU32BE bytes pos hLen
  if _hCrc : pos + 8 + len + 4 ≤ bytes.size then
    let typeStart := pos + 4
    let dataStart := pos + 8
    let dataEnd := dataStart + len
    let crcEnd := dataEnd + 4
    let typBytes := bytes.extract typeStart (typeStart + 4)
    let data := bytes.extract dataStart dataEnd
    some (typBytes, data, crcEnd)
  else
    none

def parsePngSimple (bytes : ByteArray) (_hsize : 8 <= bytes.size) :
    Option (PngHeader × ByteArray) := do
  if bytes.extract 0 8 != pngSignature then
    none
  let pos := 8
  if hLen1 : pos + 3 < bytes.size then
    match readChunk bytes pos hLen1 with
    | some (typ1, data1, pos2) =>
        if typ1 != "IHDR".toUTF8 then
          none
        if hlen : data1.size ≠ 13 then
          none
        else
          let hlen' : data1.size = 13 := by
            exact not_ne_iff.mp hlen
          let w := readU32BE data1 0 (by simp [hlen'])
          let h := readU32BE data1 4 (by simp [hlen'])
          let tail := data1.extract 8 13
          if tail != ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0] then
            none
          let hdr : PngHeader := { width := w, height := h, colorType := 2, bitDepth := 8 }
          if hLen2 : pos2 + 3 < bytes.size then
            match readChunk bytes pos2 hLen2 with
            | some (typ2, data2, pos3) =>
                if typ2 != "IDAT".toUTF8 then
                  none
                if hLen3 : pos3 + 3 < bytes.size then
                  match readChunk bytes pos3 hLen3 with
                  | some (typ3, data3, _) =>
                      if typ3 != "IEND".toUTF8 then
                        none
                      if data3.size != 0 then
                        none
                      return (hdr, data2)
                  | none =>
                      none
                else
                  none
            | none =>
                none
          else
            none
    | none =>
        none
  else
    none


partial def parsePng (bytes : ByteArray) (_hsize : 8 <= bytes.size) : Option (PngHeader × ByteArray) := do
  if let some res := parsePngSimple bytes _hsize then
    return res
  if bytes.extract 0 8 != pngSignature then
    none
  let mut pos := 8
  let mut header : Option PngHeader := none
  let mut idat := ByteArray.empty
  while pos + 8 <= bytes.size do
    if hLen : pos + 3 < bytes.size then
      let len := readU32BE bytes pos hLen
      let dataStart := pos + 8
      match readChunk bytes pos hLen with
      | some (typBytes, chunkData, posNext) =>
          if typBytes == "IHDR".toUTF8 then
            if len != 13 then
              none
            if hIH : dataStart + 12 < bytes.size then
              let w := readU32BE bytes dataStart (by omega)
              let h := readU32BE bytes (dataStart + 4) (by omega)
              let bitDepth := (bytes.get (dataStart + 8) (by omega)).toNat
              let colorType := (bytes.get (dataStart + 9) (by omega)).toNat
              let comp := (bytes.get (dataStart + 10) (by omega)).toNat
              let filter := (bytes.get (dataStart + 11) (by omega)).toNat
              let interlace := (bytes.get (dataStart + 12) (by omega)).toNat
              if comp != 0 || filter != 0 || interlace != 0 then
                none
              header := some { width := w, height := h, colorType, bitDepth }
            else
              none
          else if typBytes == "IDAT".toUTF8 then
            idat := idat ++ chunkData
          else if typBytes == "IEND".toUTF8 then
            break
          pos := posNext
      | none =>
          none
    else
      none
  match header with
  | none => none
  | some h => some (h, idat)

def paethPredictor (a b c : Nat) : Nat :=
  let p : Int := (a : Int) + (b : Int) - (c : Int)
  let pa := Int.natAbs (p - a)
  let pb := Int.natAbs (p - b)
  let pc := Int.natAbs (p - c)
  if pa <= pb && pa <= pc then a else if pb <= pc then b else c

def unfilterRow (filter : UInt8) (row : ByteArray) (prev : ByteArray) (bpp : Nat)
    (_hfilter : filter.toNat ≤ 4) : ByteArray :=
  Id.run do
    let rowLen := row.size
    let mut out := ByteArray.empty
    for i in [0:rowLen] do
      let raw := row.get! i
      let a := if i >= bpp then out.get! (i - bpp) else (0 : UInt8)
      let b := if i < prev.size then prev.get! i else (0 : UInt8)
      let c := if i >= bpp && i < prev.size then prev.get! (i - bpp) else (0 : UInt8)
      let recon :=
        match filter.toNat with
        | 0 => raw
        | 1 => u8 (raw.toNat + a.toNat)
        | 2 => u8 (raw.toNat + b.toNat)
        | 3 => u8 (raw.toNat + ((a.toNat + b.toNat) / 2))
        | 4 => u8 (raw.toNat + paethPredictor a.toNat b.toNat c.toNat)
        | _ => raw
      out := out.push recon
    return out

def decodeRowsLoop (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray := do
  if hlt : y < h then
    let filter := raw.get! offset
    let offset := offset + 1
    let rowData := raw.extract offset (offset + rowBytes)
    let offset := offset + rowBytes
    if hfilter : filter.toNat ≤ 4 then
      let row :=
        if filter.toNat = 0 then
          rowData
        else
          unfilterRow filter rowData prevRow bpp hfilter
      let pixels :=
        if bpp == 3 then
          let rowOffset := y * rowBytes
          row.copySlice 0 pixels rowOffset rowBytes
        else
          Id.run do
            let mut pixels := pixels
            for x in [0:w] do
              let base := x * bpp
              let r := row.get! base
              let g := row.get! (base + 1)
              let b := row.get! (base + 2)
              let pixBase := (y * w + x) * bytesPerPixelRGB
              pixels := pixels.set! pixBase r
              pixels := pixels.set! (pixBase + 1) g
              pixels := pixels.set! (pixBase + 2) b
            return pixels
      decodeRowsLoop raw w h bpp rowBytes (y + 1) offset row pixels
    else
      none
  else
    return pixels
termination_by h - y
decreasing_by
  have hy : y < h := hlt
  have hy' : y < y + 1 := Nat.lt_succ_self y
  exact Nat.sub_lt_sub_left hy hy'

def decodeRowsLoopRGBA (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray := do
  if hlt : y < h then
    let filter := raw.get! offset
    let offset := offset + 1
    let rowData := raw.extract offset (offset + rowBytes)
    let offset := offset + rowBytes
    if hfilter : filter.toNat ≤ 4 then
      let row :=
        if filter.toNat = 0 then
          rowData
        else
          unfilterRow filter rowData prevRow bpp hfilter
      let pixels :=
        if bpp == 4 then
          let rowOffset := y * rowBytes
          row.copySlice 0 pixels rowOffset rowBytes
        else
          Id.run do
            let mut pixels := pixels
            for x in [0:w] do
              let base := x * bpp
              let r := row.get! base
              let g := row.get! (base + 1)
              let b := row.get! (base + 2)
              let pixBase := (y * w + x) * bytesPerPixelRGBA
              pixels := pixels.set! pixBase r
              pixels := pixels.set! (pixBase + 1) g
              pixels := pixels.set! (pixBase + 2) b
              pixels := pixels.set! (pixBase + 3) (u8 255)
            return pixels
      decodeRowsLoopRGBA raw w h bpp rowBytes (y + 1) offset row pixels
    else
      none
  else
    return pixels
termination_by h - y
decreasing_by
  have hy : y < h := hlt
  have hy' : y < y + 1 := Nat.lt_succ_self y
  exact Nat.sub_lt_sub_left hy hy'

-- RGB decoder; if the source PNG is RGBA, alpha is dropped.
-- Use `decodeBitmapRGBA` to preserve alpha.
partial def decodeBitmap (bytes : ByteArray) : Option BitmapRGB8 := do
  let (hdr, idat) ←
    if hsize : 8 <= bytes.size then
      parsePng bytes hsize
    else
      none
  if hdr.bitDepth != 8 then
    none
  if hdr.colorType != 2 && hdr.colorType != 6 then
    none
  let bpp := if hdr.colorType == 2 then 3 else 4
  let raw ←
    if hsize : 2 <= idat.size then
      match zlibDecompressStored idat hsize with
      | some raw => some raw
      | none => zlibDecompress idat hsize
    else
      none
  let rowBytes := hdr.width * bpp
  let expected := hdr.height * (rowBytes + 1)
  if raw.size != expected then
    none
  let totalBytes := hdr.width * hdr.height * bytesPerPixelRGB
  let pixels0 := ByteArray.mk <| Array.replicate totalBytes 0
  let pixels ← decodeRowsLoop raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
  let size : Size := { width := hdr.width, height := hdr.height }
  if hsize : pixels.size = size.width * size.height * bytesPerPixelRGB then
    return { size, data := pixels, valid := hsize }
  else
    none

partial def decodeBitmapRGBA (bytes : ByteArray) : Option BitmapRGBA8 := do
  let (hdr, idat) ←
    if hsize : 8 <= bytes.size then
      parsePng bytes hsize
    else
      none
  if hdr.bitDepth != 8 then
    none
  if hdr.colorType != 2 && hdr.colorType != 6 then
    none
  let bpp := if hdr.colorType == 2 then 3 else 4
  let raw ←
    if hsize : 2 <= idat.size then
      match zlibDecompressStored idat hsize with
      | some raw => some raw
      | none => zlibDecompress idat hsize
    else
      none
  let rowBytes := hdr.width * bpp
  let expected := hdr.height * (rowBytes + 1)
  if raw.size != expected then
    none
  let totalBytes := hdr.width * hdr.height * bytesPerPixelRGBA
  let pixels0 := ByteArray.mk <| Array.replicate totalBytes 0
  let pixels ← decodeRowsLoopRGBA raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
  let size : Size := { width := hdr.width, height := hdr.height }
  if hsize : pixels.size = size.width * size.height * bytesPerPixelRGBA then
    return { size, data := pixels, valid := hsize }
  else
    none

def encodeRawLoop (data : ByteArray) (rowBytes h : Nat) (y : Nat) (raw : ByteArray) : ByteArray :=
  if hlt : y < h then
    let outOff := y * (rowBytes + 1)
    let start := y * rowBytes
    let raw := data.copySlice start raw (outOff + 1) rowBytes
    encodeRawLoop data rowBytes h (y + 1) raw
  else
    raw
termination_by h - y
decreasing_by
  have hy : y < h := hlt
  have hy' : y < y + 1 := Nat.lt_succ_self y
  exact Nat.sub_lt_sub_left hy hy'

def encodeRaw (bmp : BitmapRGB8) : ByteArray :=
  let w := bmp.size.width
  let h := bmp.size.height
  let rowBytes := w * bytesPerPixelRGB
  let rawSize := h * (rowBytes + 1)
  let raw := ByteArray.mk <| Array.replicate rawSize 0
  encodeRawLoop bmp.data rowBytes h 0 raw

def encodeRawRGBA (bmp : BitmapRGBA8) : ByteArray :=
  let w := bmp.size.width
  let h := bmp.size.height
  let rowBytes := w * bytesPerPixelRGBA
  let rawSize := h * (rowBytes + 1)
  let raw := ByteArray.mk <| Array.replicate rawSize 0
  encodeRawLoop bmp.data rowBytes h 0 raw

def encodeBitmap (bmp : BitmapRGB8) : ByteArray :=
  Id.run do
    let w := bmp.size.width
    let h := bmp.size.height
    let raw := encodeRaw bmp
    let ihdr := u32be w ++ u32be h ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
    let idat := zlibCompressStored raw
    pngSignature
      ++ mkChunk "IHDR" ihdr
      ++ mkChunk "IDAT" idat
      ++ mkChunk "IEND" ByteArray.empty

def encodeBitmapRGBA (bmp : BitmapRGBA8) : ByteArray :=
  Id.run do
    let w := bmp.size.width
    let h := bmp.size.height
    let raw := encodeRawRGBA bmp
    let ihdr := u32be w ++ u32be h ++ ByteArray.mk #[u8 8, u8 6, u8 0, u8 0, u8 0]
    let idat := zlibCompressStored raw
    pngSignature
      ++ mkChunk "IHDR" ihdr
      ++ mkChunk "IDAT" idat
      ++ mkChunk "IEND" ByteArray.empty

end Png

def BitmapRGB8.readPng (path : FilePath) : IO (Except String BitmapRGB8) := do
  let bytesOrErr <- ioToExcept (IO.FS.readBinFile path)
  match bytesOrErr with
  | Except.error err => pure (Except.error err)
  | Except.ok bytes =>
      match Png.decodeBitmap bytes with
      | some bmp => pure (Except.ok bmp)
      | none => pure (Except.error "invalid PNG bitmap")

def BitmapRGB8.writePng (path : FilePath) (bmp : BitmapRGB8) : IO (Except String Unit) :=
  ioToExcept (IO.FS.writeBinFile path (Png.encodeBitmap bmp))

instance : FileWritable BitmapRGB8 where
  write := BitmapRGB8.writePng

instance : FileReadable BitmapRGB8 where
  read := BitmapRGB8.readPng

def BitmapRGBA8.readPng (path : FilePath) : IO (Except String BitmapRGBA8) := do
  let bytesOrErr <- ioToExcept (IO.FS.readBinFile path)
  match bytesOrErr with
  | Except.error err => pure (Except.error err)
  | Except.ok bytes =>
      match Png.decodeBitmapRGBA bytes with
      | some bmp => pure (Except.ok bmp)
      | none => pure (Except.error "invalid PNG bitmap")

def BitmapRGBA8.writePng (path : FilePath) (bmp : BitmapRGBA8) : IO (Except String Unit) :=
  ioToExcept (IO.FS.writeBinFile path (Png.encodeBitmapRGBA bmp))

instance : FileWritable BitmapRGBA8 where
  write := BitmapRGBA8.writePng

instance : FileReadable BitmapRGBA8 where
  read := BitmapRGBA8.readPng

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Verification. Converting tests into proofs.
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html

variable (aPixel : PixelRGB8)

example : (mkBlankBitmap 1 1 aPixel).data.size = bytesPerPixelRGB := by
  simpa [bytesPerPixelRGB] using (mkBlankBitmap 1 1 aPixel).valid

end Bitmaps
