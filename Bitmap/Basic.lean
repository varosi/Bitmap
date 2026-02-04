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

instance : Inhabited PixelRGB8 := instInhabitedPixelRGB _
instance : DecidableEq PixelRGB8 := by
  unfold PixelRGB8
  infer_instance

-------------------------------------------------------------------------------
def bytesPerPixel : Nat := 3

structure Bitmap where
  mk ::

  size : Size
  data : ByteArray

  valid : data.size = size.width * size.height * bytesPerPixel := by
    simp [bytesPerPixel]
deriving Repr, DecidableEq

abbrev BitmapRGB8 := Bitmap

instance : DecidableEq BitmapRGB8 := by
  infer_instance

lemma byteArray_size_set {bs : ByteArray} {i : Nat} {h : i < bs.size} {b : UInt8} :
    (bs.set i b h).size = bs.size := by
  cases bs with
  | mk data =>
      simp [ByteArray.set, ByteArray.size, Array.size_set]

def putPixel (img : Bitmap) (x y : UInt32) (pixel : PixelRGB8)
    (h1 : x.toNat < img.size.width) (h2: y.toNat < img.size.height) : Bitmap := by
  let pixIdx := x.toNat + y.toNat * img.size.width
  have hPix : pixIdx < img.size.width * img.size.height := by
    have hx' :
        x.toNat + y.toNat * img.size.width <
          img.size.width + y.toNat * img.size.width := Nat.add_lt_add_right h1 _
    have hx'' :
        x.toNat + y.toNat * img.size.width <
          img.size.width * (1 + y.toNat) := by
      calc
        x.toNat + y.toNat * img.size.width <
            img.size.width + y.toNat * img.size.width := hx'
        _ = img.size.width * (1 + y.toNat) := by
            simp [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    have hy' :
        img.size.width * (1 + y.toNat) ≤ img.size.width * img.size.height := by
      apply Nat.mul_le_mul_left
      have hyle : y.toNat + 1 ≤ img.size.height := Nat.succ_le_of_lt h2
      simpa [Nat.add_comm] using hyle
    have hlt :
        x.toNat + y.toNat * img.size.width <
          img.size.width * img.size.height := lt_of_lt_of_le hx'' hy'
    simpa [pixIdx] using hlt

  let base := pixIdx * bytesPerPixel
  have h2' : base + 2 < img.data.size := by
    have : pixIdx * bytesPerPixel + 2 < img.size.width * img.size.height * bytesPerPixel := by
      have hPix' := hPix
      simp [bytesPerPixel] at hPix' ⊢
      omega
    simpa [base, img.valid] using this
  have h1' : base + 1 < img.data.size := by
    omega
  have h0' : base < img.data.size := by
    omega

  let data1 := img.data.set base pixel.r h0'
  have h1'' : base + 1 < data1.size := by
    simpa [data1, byteArray_size_set] using h1'
  let data2 := data1.set (base + 1) pixel.g h1''
  have h2'' : base + 2 < data2.size := by
    simpa [data2, data1, byteArray_size_set] using h2'
  let data3 := data2.set (base + 2) pixel.b h2''
  have hsize : data3.size = img.data.size := by
    simp [data3, data2, data1, byteArray_size_set]

  exact { img with data := data3, valid := by simpa [hsize] using img.valid }

def getPixel (img : Bitmap) (x y : UInt32)
    (hx : x.toNat < img.size.width)
    (hy : y.toNat < img.size.height) : PixelRGB8 := by
  let pixIdx := x.toNat + y.toNat * img.size.width
  have hPix : pixIdx < img.size.width * img.size.height := by
    have hx' :
        x.toNat + y.toNat * img.size.width <
          img.size.width + y.toNat * img.size.width := Nat.add_lt_add_right hx _
    have hx'' :
        x.toNat + y.toNat * img.size.width <
          img.size.width * (1 + y.toNat) := by
      calc
        x.toNat + y.toNat * img.size.width <
            img.size.width + y.toNat * img.size.width := hx'
        _ = img.size.width * (1 + y.toNat) := by
            simp [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    have hy' :
        img.size.width * (1 + y.toNat) ≤ img.size.width * img.size.height := by
      apply Nat.mul_le_mul_left
      have hyle : y.toNat + 1 ≤ img.size.height := Nat.succ_le_of_lt hy
      simpa [Nat.add_comm] using hyle
    have hlt :
        x.toNat + y.toNat * img.size.width <
          img.size.width * img.size.height := lt_of_lt_of_le hx'' hy'
    simpa [pixIdx] using hlt

  let base := pixIdx * bytesPerPixel
  have h2' : base + 2 < img.data.size := by
    have : pixIdx * bytesPerPixel + 2 < img.size.width * img.size.height * bytesPerPixel := by
      have hPix' := hPix
      simp [bytesPerPixel] at hPix' ⊢
      omega
    simpa [base, img.valid] using this
  have h1' : base + 1 < img.data.size := by
    omega
  have h0' : base < img.data.size := by
    omega

  exact { r := img.data.get base h0'
          g := img.data.get (base + 1) h1'
          b := img.data.get (base + 2) h2' }

def Bitmap.ofPixelFn (w h : Nat) (f : Fin (w * h) → PixelRGB8) : Bitmap := by
  refine
    { size := { width := w, height := h }
      data := ByteArray.mk <| Array.ofFn (fun i : Fin (w * h * bytesPerPixel) =>
        let pixIdx := i.val / bytesPerPixel
        have hidx : pixIdx < w * h := by
          have hlt : i.val < bytesPerPixel * (w * h) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using i.isLt
          exact Nat.div_lt_of_lt_mul hlt
        let px := f ⟨pixIdx, hidx⟩
        match i.val % bytesPerPixel with
        | 0 => px.r
        | 1 => px.g
        | _ => px.b)
      valid := ?_ }
  simp [bytesPerPixel, ByteArray.size, Array.size_ofFn, Nat.mul_assoc]

def mkBlankBitmap (w h : ℕ) (color : PixelRGB8) : Bitmap :=
  Bitmap.ofPixelFn w h (fun _ => color)

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
  ByteArray.mk #[u8 (n &&& 0xFF), u8 ((n >>> 8) &&& 0xFF)]

def u32be (n : Nat) : ByteArray :=
  ByteArray.mk #[
    u8 ((n >>> 24) &&& 0xFF),
    u8 ((n >>> 16) &&& 0xFF),
    u8 ((n >>> 8) &&& 0xFF),
    u8 (n &&& 0xFF)
  ]

def readU16LE (bytes : ByteArray) (pos : Nat) (h : pos + 1 < bytes.size) : Nat :=
  let h0 : pos < bytes.size := by omega
  let b0 := bytes.get pos h0
  let b1 := bytes.get (pos + 1) (by simpa using h)
  b0.toNat + (b1.toNat <<< 8)

def readU32BE (bytes : ByteArray) (pos : Nat) (h : pos + 3 < bytes.size) : Nat :=
  let h2 : pos + 2 < bytes.size := by omega
  let h1 : pos + 1 < bytes.size := by omega
  let h0 : pos < bytes.size := by omega
  let b0 := bytes.get pos h0
  let b1 := bytes.get (pos + 1) (by simpa using h1)
  let b2 := bytes.get (pos + 2) (by simpa using h2)
  let b3 := bytes.get (pos + 3) (by simpa using h)
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

def deflateStored (raw : ByteArray) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    let mut pos := 0
    while pos < raw.size do
      let remaining := raw.size - pos
      let blockLen := if remaining > 65535 then 65535 else remaining
      let final := (pos + blockLen == raw.size)
      out := out.push (if final then u8 0x01 else u8 0x00)
      out := out ++ u16le blockLen
      out := out ++ u16le (0xFFFF - blockLen)
      out := out ++ raw.extract pos (pos + blockLen)
      pos := pos + blockLen
    return out

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

lemma bitIndex_readBit (br : BitReader) (h : br.bytePos < br.data.size) :
    (BitReader.readBit br).2.bitIndex = br.bitIndex + 1 := by
  unfold BitReader.readBit BitReader.bitIndex
  have hne : br.bytePos ≠ br.data.size := ne_of_lt h
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

lemma readBit_data (br : BitReader) (h : br.bytePos < br.data.size) :
    (br.readBit).2.data = br.data := by
  unfold BitReader.readBit
  have hne : br.bytePos ≠ br.data.size := ne_of_lt h
  by_cases hnext : br.bitPos + 1 = 8 <;> simp [hne, hnext]

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
          have hindex : br'.bitIndex = br.bitIndex + 1 := by
            simpa [hres] using bitIndex_readBit br hbyte
          have hdata : br'.data = br.data := by
            simpa [hres] using readBit_data br hbyte
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

lemma lengthBases_size : lengthBases.size = 29 := by decide
lemma lengthExtra_size : lengthExtra.size = 29 := by decide
lemma distBases_size : distBases.size = 30 := by decide
lemma distExtra_size : distExtra.size = 30 := by decide

def decodeLength (sym : Nat) (br : BitReader)
    (h : 257 ≤ sym ∧ sym ≤ 285)
    (hbits : br.bitIndex + (lengthExtra[(sym - 257)]'
      (by
        have hidxlt : sym - 257 < 29 := by omega
        simpa [lengthExtra_size] using hidxlt)) <= br.data.size * 8) :
    Nat × BitReader :=
  let idx := sym - 257
  have hidxle : idx ≤ 28 := by
    dsimp [idx]
    omega
  have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
  have hidxBase : idx < lengthBases.size := by simpa [lengthBases_size] using hidxlt
  have hidxExtra : idx < lengthExtra.size := by simpa [lengthExtra_size] using hidxlt
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
        simpa [distExtra_size, distBases_size] using h) <= br.data.size * 8) :
    Nat × BitReader :=
  have hdistExtra : sym < distExtra.size := by
    simpa [distExtra_size, distBases_size] using h
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
      have hidxExtra : idx < lengthExtra.size := by simpa [lengthExtra_size] using hidxlt
      let extra := Array.getInternal lengthExtra idx hidxExtra
      if hbits : br.bitIndex + extra <= br.data.size * 8 then
        let (len, br'') := decodeLength sym br hlen (by simpa using hbits)
        br := br''
        let (distSym, br''') ← dist.decode br
        br := br'''
        if hdist : distSym < distBases.size then
          let extraD := Array.getInternal distExtra distSym (by
            simpa [distExtra_size, distBases_size] using hdist)
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

structure PngHeader where
  width : Nat
  height : Nat
  colorType : Nat
  bitDepth : Nat
deriving Repr

partial def parsePng (bytes : ByteArray) (_hsize : 8 <= bytes.size) : Option (PngHeader × ByteArray) := do
  if bytes.extract 0 8 != pngSignature then
    none
  let mut pos := 8
  let mut header : Option PngHeader := none
  let mut idat := ByteArray.empty
  while pos + 8 <= bytes.size do
    if hLen : pos + 3 < bytes.size then
      let len := readU32BE bytes pos hLen
      let typeStart := pos + 4
      let dataStart := pos + 8
      let dataEnd := dataStart + len
      let crcEnd := dataEnd + 4
      if crcEnd > bytes.size then
        none
      let typBytes := bytes.extract typeStart (typeStart + 4)
      let typ := String.fromUTF8! typBytes
      let chunkData := bytes.extract dataStart dataEnd
      if typ == "IHDR" then
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
      else if typ == "IDAT" then
        idat := idat ++ chunkData
      else if typ == "IEND" then
        break
      pos := crcEnd
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
      zlibDecompress idat hsize
    else
      none
  let rowBytes := hdr.width * bpp
  let expected := hdr.height * (rowBytes + 1)
  if raw.size != expected then
    none
  let mut pixels := ByteArray.empty
  let mut prevRow := ByteArray.empty
  let mut offset := 0
  for _y in [0:hdr.height] do
    let filter := raw.get! offset
    offset := offset + 1
    let rowData := raw.extract offset (offset + rowBytes)
    offset := offset + rowBytes
    if hfilter : filter.toNat ≤ 4 then
      let row := unfilterRow filter rowData prevRow bpp hfilter
      let mut x := 0
      while x < hdr.width do
        let base := x * bpp
        let r := row.get! base
        let g := row.get! (base + 1)
        let b := row.get! (base + 2)
        pixels := pixels.push r
        pixels := pixels.push g
        pixels := pixels.push b
        x := x + 1
      prevRow := row
    else
      none
  let size : Size := { width := hdr.width, height := hdr.height }
  if hsize : pixels.size = size.width * size.height * bytesPerPixel then
    return { size, data := pixels, valid := hsize }
  else
    none

def encodeBitmap (bmp : BitmapRGB8) : ByteArray :=
  Id.run do
    let w := bmp.size.width
    let h := bmp.size.height
    let rowBytes := w * bytesPerPixel
    let mut raw := ByteArray.empty
    for y in [0:h] do
      raw := raw.push 0
      let start := y * rowBytes
      raw := raw ++ bmp.data.extract start (start + rowBytes)
    let ihdr := u32be w ++ u32be h ++ ByteArray.mk #[u8 8, u8 2, u8 0, u8 0, u8 0]
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

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Verification. Converting tests into proofs.
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html

variable (aPixel : PixelRGB8)

example : (mkBlankBitmap 1 1 aPixel).data.size = bytesPerPixel := by
  simpa [bytesPerPixel] using (mkBlankBitmap 1 1 aPixel).valid

end Bitmaps
