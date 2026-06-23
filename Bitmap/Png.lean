import Bitmap.Basic
import Std.Time

open System (FilePath)

universe u

namespace Bitmaps

-------------------------------------------------------------------------------
-- PNG read/write for BitmapRGB8

namespace Png

def uint16MaxValue : Nat := UInt16.size - 1

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

def crc32Update (c : UInt32) (bytes : ByteArray) : UInt32 :=
  ByteArray.foldl
    (fun c b =>
      let idx : Nat := ((c ^^^ (UInt32.ofNat b.toNat)) &&& (0xFF : UInt32)).toNat
      crc32Table[idx]! ^^^ (c >>> 8))
    c
    bytes

def crc32 (bytes : ByteArray) : UInt32 :=
  (crc32Update 0xFFFFFFFF bytes) ^^^ 0xFFFFFFFF

def crc32Chunk (typBytes data : ByteArray) : UInt32 :=
  (crc32Update (crc32Update 0xFFFFFFFF typBytes) data) ^^^ 0xFFFFFFFF

def adler32Fast (bytes : ByteArray) : UInt32 :=
  Id.run do
    let mod : Nat := 65521
    let chunk : Nat := 5552
    let data := bytes.data
    let mut i : Nat := 0
    let mut a : Nat := 1
    let mut b : Nat := 0
    while i < data.size do
      let stop := Nat.min data.size (i + chunk)
      while i < stop do
        let byte := data[i]!
        a := a + byte.toNat
        b := b + a
        i := i + 1
      a := a % mod
      b := b % mod
    return UInt32.ofNat ((b <<< 16) + a)

def adler32 (bytes : ByteArray) : UInt32 :=
  adler32Fast bytes

def pngSignature : ByteArray :=
  ByteArray.mk #[
    u8 0x89, u8 0x50, u8 0x4E, u8 0x47,
    u8 0x0D, u8 0x0A, u8 0x1A, u8 0x0A
  ]

def ihdrTypeBytes : ByteArray := "IHDR".toUTF8
def idatTypeBytes : ByteArray := "IDAT".toUTF8
def iendTypeBytes : ByteArray := "IEND".toUTF8
def plteTypeBytes : ByteArray := "PLTE".toUTF8
def trnsTypeBytes : ByteArray := "tRNS".toUTF8
def bkgdTypeBytes : ByteArray := "bKGD".toUTF8
def gamaTypeBytes : ByteArray := "gAMA".toUTF8
def chrmTypeBytes : ByteArray := "cHRM".toUTF8
def srgbTypeBytes : ByteArray := "sRGB".toUTF8
def sbitTypeBytes : ByteArray := "sBIT".toUTF8
def timeTypeBytes : ByteArray := "tIME".toUTF8
def physTypeBytes : ByteArray := "pHYs".toUTF8

structure PngTime where
  year : Nat
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Nat
deriving Repr, DecidableEq

def pngTimeLeapYear (year : Nat) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

def pngTimeDaysInMonth (year month : Nat) : Nat :=
  if month == 1 then
    31
  else if month == 2 then
    if pngTimeLeapYear year then 29 else 28
  else if month == 3 then
    31
  else if month == 4 then
    30
  else if month == 5 then
    31
  else if month == 6 then
    30
  else if month == 7 then
    31
  else if month == 8 then
    31
  else if month == 9 then
    30
  else if month == 10 then
    31
  else if month == 11 then
    30
  else if month == 12 then
    31
  else
    0

def PngTime.valid (time : PngTime) : Bool :=
  decide (time.year ≤ uint16MaxValue) &&
  decide (1 ≤ time.month) && decide (time.month ≤ 12) &&
  decide (1 ≤ time.day) && decide (time.day ≤ pngTimeDaysInMonth time.year time.month) &&
  decide (time.hour < 24) &&
  decide (time.minute < 60) &&
  decide (time.second ≤ 60)

def encodeTimeData? (time : PngTime) : Option ByteArray :=
  if time.valid then
    some <| ByteArray.mk #[
      u8 (time.year / 256), u8 time.year,
      u8 time.month, u8 time.day, u8 time.hour, u8 time.minute, u8 time.second
    ]
  else
    none

inductive PngPhysicalUnit where
  | unknown
  | meter
deriving Repr, DecidableEq

def PngPhysicalUnit.toByte : PngPhysicalUnit -> UInt8
  | .unknown => u8 0
  | .meter => u8 1

def PngPhysicalUnit.ofByte (b : UInt8) : Option PngPhysicalUnit :=
  if b == u8 0 then
    some .unknown
  else if b == u8 1 then
    some .meter
  else
    none

structure PngPhysicalPixelDimensions where
  xPixelsPerUnit : Nat
  yPixelsPerUnit : Nat
  unit : PngPhysicalUnit
deriving Repr, DecidableEq

def PngPhysicalPixelDimensions.valid (physical : PngPhysicalPixelDimensions) : Bool :=
  decide (physical.xPixelsPerUnit < UInt32.size) &&
  decide (physical.yPixelsPerUnit < UInt32.size)

def dpiToPixelsPerMeterRounded (dpi : Nat) : Nat :=
  (dpi * 10000 + 127) / 254

def pixelsPerMeterToDpiRounded (pixelsPerMeter : Nat) : Nat :=
  (pixelsPerMeter * 254 + 5000) / 10000

def PngPhysicalPixelDimensions.ofDpiRounded (xDpi yDpi : Nat) : PngPhysicalPixelDimensions :=
  { xPixelsPerUnit := dpiToPixelsPerMeterRounded xDpi
    yPixelsPerUnit := dpiToPixelsPerMeterRounded yDpi
    unit := .meter }

def PngPhysicalPixelDimensions.dpi? (physical : PngPhysicalPixelDimensions) :
    Option (Nat × Nat) :=
  match physical.unit with
  | .unknown => none
  | .meter =>
      some (pixelsPerMeterToDpiRounded physical.xPixelsPerUnit,
        pixelsPerMeterToDpiRounded physical.yPixelsPerUnit)

def signed32InRange (n : Int) : Bool :=
  decide (Int32.minValue.toInt ≤ n ∧ n ≤ Int32.maxValue.toInt)

def signed32ToU32? (n : Int) : Option Nat :=
  if signed32InRange n then
    some (Int32.ofInt n).toUInt32.toNat
  else
    none

structure PngChromaticityPoint where
  x : Int
  y : Int
deriving Repr, DecidableEq

def PngChromaticityPoint.valid (p : PngChromaticityPoint) : Bool :=
  signed32InRange p.x && signed32InRange p.y

structure PngChromaticities where
  white : PngChromaticityPoint
  red : PngChromaticityPoint
  green : PngChromaticityPoint
  blue : PngChromaticityPoint
deriving Repr, DecidableEq

def PngChromaticities.valid (c : PngChromaticities) : Bool :=
  c.white.valid && c.red.valid && c.green.valid && c.blue.valid

def PngChromaticities.srgb : PngChromaticities :=
  { white := { x := 31270, y := 32900 }
    red := { x := 64000, y := 33000 }
    green := { x := 30000, y := 60000 }
    blue := { x := 15000, y := 6000 } }

def mkChunkBytes (typBytes : ByteArray) (data : ByteArray) : ByteArray :=
  let lenBytes := u32be data.size
  let crc := crc32Chunk typBytes data
  let outSize := lenBytes.size + typBytes.size + data.size + 4
  let out := ByteArray.emptyWithCapacity outSize
  out ++ lenBytes ++ typBytes ++ data ++ u32be crc.toNat

def mkChunk (typ : String) (data : ByteArray) : ByteArray :=
  mkChunkBytes typ.toUTF8 data

def storedBlock (payload : ByteArray) (final : Bool) : ByteArray :=
  let len := payload.size
  ByteArray.mk #[if final then u8 0x01 else u8 0x00]
    ++ u16le len ++ u16le (uint16MaxValue - len) ++ payload

def deflateStoredFastAux (raw : ByteArray) (out : ByteArray) : ByteArray :=
  if _hzero : raw.size = 0 then
    out ++ storedBlock ByteArray.empty true
  else
    let blockLen := Nat.min uint16MaxValue raw.size
    let final := blockLen == raw.size
    let payload := raw.extract 0 blockLen
    let block := storedBlock payload final
    if _hfinal : final then
      out ++ block
    else
      deflateStoredFastAux (raw.extract blockLen raw.size) (out ++ block)
termination_by raw.size
decreasing_by
  have hle : blockLen ≤ raw.size := by
    simpa [blockLen] using Nat.min_le_right uint16MaxValue raw.size
  have hpos : 0 < blockLen := by
    have hpos_raw : 0 < raw.size := Nat.pos_of_ne_zero _hzero
    have hpos_max : 0 < uint16MaxValue := by
      simp [uint16MaxValue, UInt16.size]
    rw [Nat.lt_min]
    exact ⟨hpos_max, hpos_raw⟩
  simp [ByteArray.size_extract]
  exact Nat.sub_lt_self hpos hle

def deflateStored (raw : ByteArray) : ByteArray :=
  if _hzero : raw.size = 0 then
    storedBlock ByteArray.empty true
  else
    let blockLen := Nat.min uint16MaxValue raw.size
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
    simpa [blockLen] using Nat.min_le_right uint16MaxValue raw.size
  have hpos : 0 < blockLen := by
    have hpos_raw : 0 < raw.size := Nat.pos_of_ne_zero _hzero
    have hpos_max : 0 < uint16MaxValue := by
      simp [uint16MaxValue, UInt16.size]
    rw [Nat.lt_min]
    exact ⟨hpos_max, hpos_raw⟩
  simp [ByteArray.size_extract]
  exact Nat.sub_lt_self hpos hle

def deflateStoredFast (raw : ByteArray) : ByteArray :=
  deflateStoredFastAux raw ByteArray.empty

inductive PngEncodeMode
  | stored
  | fixed
  | dynamic
deriving Repr, DecidableEq

inductive PngSrgbIntent
  | perceptual
  | relativeColorimetric
  | saturation
  | absoluteColorimetric
deriving Repr, DecidableEq

def PngSrgbIntent.toByte : PngSrgbIntent -> UInt8
  | .perceptual => u8 0
  | .relativeColorimetric => u8 1
  | .saturation => u8 2
  | .absoluteColorimetric => u8 3

def PngSrgbIntent.ofByte (b : UInt8) : Option PngSrgbIntent :=
  if b == u8 0 then
    some .perceptual
  else if b == u8 1 then
    some .relativeColorimetric
  else if b == u8 2 then
    some .saturation
  else if b == u8 3 then
    some .absoluteColorimetric
  else
    none

inductive PngEncodeColorSpace
  | gamma (gammaScaled : Nat)
  | srgb (intent : PngSrgbIntent) (includeCompatGamma : Bool)
deriving Repr, DecidableEq

inductive PngRowFilter
  | none
  | sub
  | up
  | average
  | paeth
deriving Repr, DecidableEq

def PngRowFilter.toByte : PngRowFilter -> UInt8
  | .none => u8 0
  | .sub => u8 1
  | .up => u8 2
  | .average => u8 3
  | .paeth => u8 4

inductive PngFilterStrategy
  | none
  | fixed (filter : PngRowFilter)
  | adaptive
deriving Repr, DecidableEq

structure PngEncodeOptions where
  mode : PngEncodeMode := .fixed
  colorSpace : Option PngEncodeColorSpace := none
  chromaticities : Option PngChromaticities := none
  filter : PngFilterStrategy := .none
  physical : Option PngPhysicalPixelDimensions := none
  modificationTime : Option PngTime := none
deriving Repr, DecidableEq

structure BitWriter where
  out : ByteArray
  cur : UInt8
  bitPos : Nat
  hbit : bitPos < 8
deriving Repr, DecidableEq

def BitWriter.empty : BitWriter :=
  { out := ByteArray.empty, cur := 0, bitPos := 0, hbit := by decide }

def BitWriter.writeBit (bw : BitWriter) (bit : Nat) : BitWriter :=
  let cur := bw.cur ||| UInt8.ofNat ((bit % 2) <<< bw.bitPos)
  if h7 : bw.bitPos = 7 then
    { out := bw.out.push cur, cur := 0, bitPos := 0, hbit := by decide }
  else
    let hle : bw.bitPos ≤ 7 := Nat.le_of_lt_succ bw.hbit
    let hlt : bw.bitPos < 7 := lt_of_le_of_ne hle h7
    let hbit' : bw.bitPos + 1 < 8 := by
      simpa [Nat.succ_eq_add_one] using (Nat.succ_lt_succ_iff.mpr hlt)
    { bw with cur := cur, bitPos := bw.bitPos + 1, hbit := hbit' }

def BitWriter.writeBits (bw : BitWriter) (bits len : Nat) : BitWriter :=
  match len with
  | 0 => bw
  | n + 1 => BitWriter.writeBits (bw.writeBit (bits % 2)) (bits >>> 1) n

def packBitsAccU8 (bits len shift : Nat) (acc : UInt8) : UInt8 :=
  match len with
  | 0 => acc
  | n + 1 =>
      packBitsAccU8 (bits >>> 1) n (shift + 1)
        (acc ||| UInt8.ofNat ((bits % 2) <<< shift))

def BitWriter.writeBitsFast (bw : BitWriter) (bits len : Nat) : BitWriter :=
  if hsmall : bw.bitPos + len < 8 then
    let cur := packBitsAccU8 bits len bw.bitPos bw.cur
    { bw with cur := cur, bitPos := bw.bitPos + len, hbit := by omega }
  else
    let k := 8 - bw.bitPos
    let byte := packBitsAccU8 bits k bw.bitPos bw.cur
    let bw' : BitWriter :=
      { out := bw.out.push byte, cur := 0, bitPos := 0, hbit := by decide }
    writeBitsFast bw' (bits >>> k) (len - k)
termination_by len
decreasing_by
  have hlt : 0 < 8 - bw.bitPos := by
    have hpos : bw.bitPos < 8 := bw.hbit
    omega
  have hle : 8 - bw.bitPos ≤ len := by
    omega
  exact Nat.sub_lt_self hlt hle

def BitWriter.flush (bw : BitWriter) : ByteArray :=
  if bw.bitPos = 0 then
    bw.out
  else
    bw.out.push bw.cur

def reverseBitsAux (code len res : Nat) : Nat :=
  match len with
  | 0 => res
  | n + 1 =>
      reverseBitsAux (code >>> 1) n (Nat.bit (code.testBit 0) res)

def reverseBits (code len : Nat) : Nat :=
  reverseBitsAux code len 0

-- Fixed Huffman literal/length code (code, bit-length).
def fixedLitLenCode (sym : Nat) : Nat × Nat :=
  if sym ≤ 143 then
    (sym + 48, 8)
  else if sym ≤ 255 then
    (sym - 144 + 400, 9)
  else if sym ≤ 279 then
    (sym - 256, 7)
  else
    (sym - 280 + 192, 8)

def deflateFixedAux (data : Array UInt8) (i : Nat) (bw : BitWriter) : BitWriter :=
  if h : i < data.size then
    let b := data[i]
    let (code, len) := fixedLitLenCode b.toNat
    deflateFixedAux data (i + 1) (bw.writeBitsFast (reverseBits code len) len)
  else
    bw
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  have hle : data.size - (i + 1) < data.size - i := by
    exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
  exact hle

def fixedLitLenRevTable : Array (Nat × Nat) :=
  Array.ofFn (fun i : Fin 288 =>
    let (code, len) := fixedLitLenCode i.val
    (reverseBits code len, len))

def fixedLitLenRevCodeFast (sym : Nat) : Nat × Nat :=
  if h : sym < fixedLitLenRevTable.size then
    Array.getInternal fixedLitLenRevTable sym h
  else
    let (code, len) := fixedLitLenCode sym
    (reverseBits code len, len)

-- Map a deflate match length in [3, 258] to
-- (literal/length symbol, extra bits value, extra bits width).
def fixedLenMatchInfo (len : Nat) : Nat × Nat × Nat :=
  if len <= 10 then
    (len + 254, 0, 0)
  else if len <= 12 then
    (265, len - 11, 1)
  else if len <= 14 then
    (266, len - 13, 1)
  else if len <= 16 then
    (267, len - 15, 1)
  else if len <= 18 then
    (268, len - 17, 1)
  else if len <= 22 then
    (269, len - 19, 2)
  else if len <= 26 then
    (270, len - 23, 2)
  else if len <= 30 then
    (271, len - 27, 2)
  else if len <= 34 then
    (272, len - 31, 2)
  else if len <= 42 then
    (273, len - 35, 3)
  else if len <= 50 then
    (274, len - 43, 3)
  else if len <= 58 then
    (275, len - 51, 3)
  else if len <= 66 then
    (276, len - 59, 3)
  else if len <= 82 then
    (277, len - 67, 4)
  else if len <= 98 then
    (278, len - 83, 4)
  else if len <= 114 then
    (279, len - 99, 4)
  else if len <= 130 then
    (280, len - 115, 4)
  else if len <= 162 then
    (281, len - 131, 5)
  else if len <= 194 then
    (282, len - 163, 5)
  else if len <= 226 then
    (283, len - 195, 5)
  else if len <= 257 then
    (284, len - 227, 5)
  else
    (285, 0, 0)

def deflateMinMatchLen : Nat := 3

def deflateMaxMatchLen : Nat := 258

def deflateMaxDistance : Nat := 32768

def deflateHashBucketCount : Nat := 32768

def deflateDistanceBases : Array Nat :=
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

def deflateDistanceExtraLens : Array Nat :=
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

def deflateLengthInfo (len : Nat) : Nat × Nat × Nat :=
  fixedLenMatchInfo len

def deflateDistanceInfoSearch (distance sym : Nat) : Option (Nat × Nat × Nat) :=
  if h : sym < deflateDistanceBases.size then
    let base := deflateDistanceBases[sym]
    let extraLen := deflateDistanceExtraLens[sym]!
    let limit := base + (1 <<< extraLen)
    if base ≤ distance && distance < limit then
      some (sym, distance - base, extraLen)
    else
      deflateDistanceInfoSearch distance (sym + 1)
  else
    none
termination_by deflateDistanceBases.size - sym
decreasing_by
  have hlt : sym < deflateDistanceBases.size := h
  exact Nat.sub_lt_sub_left (k := sym) (m := deflateDistanceBases.size)
    (n := sym + 1) hlt (Nat.lt_succ_self sym)

def deflateDistanceInfo? (distance : Nat) : Option (Nat × Nat × Nat) :=
  if 1 ≤ distance && distance ≤ deflateMaxDistance then
    deflateDistanceInfoSearch distance 0
  else
    none

def deflateDistanceInfo (distance : Nat) : Nat × Nat × Nat :=
  match deflateDistanceInfo? distance with
  | some info => info
  | none => (0, 0, 0)

@[inline] def BitWriter.writeFixedLiteralFast (bw : BitWriter) (b : UInt8) : BitWriter :=
  let (bits, len) := fixedLitLenRevCodeFast b.toNat
  bw.writeBitsFast bits len

@[inline] def BitWriter.writeFixedMatchDist1Fast (bw : BitWriter) (matchLen : Nat) : BitWriter :=
  let (sym, extraBits, extraLen) := fixedLenMatchInfo matchLen
  let (symBits, symLen) := fixedLitLenRevCodeFast sym
  let bw := bw.writeBitsFast symBits symLen
  let bw := bw.writeBitsFast extraBits extraLen
  -- Fixed-Huffman distance symbol 0 encodes distance = 1.
  bw.writeBitsFast 0 5

@[inline] def BitWriter.writeFixedMatchFast (bw : BitWriter) (matchLen distance : Nat) : BitWriter :=
  let (sym, extraBits, extraLen) := deflateLengthInfo matchLen
  let (symBits, symLen) := fixedLitLenRevCodeFast sym
  let bw := bw.writeBitsFast symBits symLen
  let bw := bw.writeBitsFast extraBits extraLen
  match deflateDistanceInfo? distance with
  | some (distSym, distExtraBits, distExtraLen) =>
      let bw := bw.writeBitsFast (reverseBits distSym 5) 5
      bw.writeBitsFast distExtraBits distExtraLen
  | none =>
      bw.writeBitsFast 0 5

@[inline] def chooseFixedMatchChunkLen (remaining : Nat) : Nat :=
  if remaining > 258 then
    let r := remaining % 258
    if r == 1 then 256
    else if r == 2 then 257
    else 258
  else
    remaining

@[inline] def quadTailEqbFast (data : Array UInt8) (i : Nat) (b : UInt8) (h3 : i + 3 < data.size) :
    Bool :=
  let b1 := data[i + 1]'(by omega)
  let b2 := data[i + 2]'(by omega)
  let b3 := data[i + 3]'h3
  (b1 == b) && (b2 == b) && (b3 == b)

def sameByteRunEndFast (data : Array UInt8) (b : UInt8) (j : Nat) : Nat :=
  if h : j < data.size then
    if data[j]'h = b then
      sameByteRunEndFast data b (j + 1)
    else
      j
  else
    j
termination_by data.size - j
decreasing_by
  have hlt : j < data.size := h
  exact Nat.sub_lt_sub_left (k := j) (m := data.size) (n := j + 1) hlt (Nat.lt_succ_self j)

def BitWriter.writeFixedLiteralRepeatFast (bw : BitWriter) (b : UInt8) (n : Nat) : BitWriter :=
  match n with
  | 0 => bw
  | n + 1 => (bw.writeFixedLiteralFast b).writeFixedLiteralRepeatFast b n

def BitWriter.writeFixedMatchDist1ChunksFast (bw : BitWriter) (remaining : Nat) : BitWriter :=
  if _h : 3 ≤ remaining then
    let chunk := chooseFixedMatchChunkLen remaining
    (bw.writeFixedMatchDist1Fast chunk).writeFixedMatchDist1ChunksFast (remaining - chunk)
  else
    bw
termination_by remaining
decreasing_by
  by_cases hgt : remaining > 258
  · by_cases hr1 : (remaining % 258 == 1)
    · have hchunk : chooseFixedMatchChunkLen remaining = 256 := by
        simp [chooseFixedMatchChunkLen, hgt, hr1]
      omega
    · by_cases hr2 : (remaining % 258 == 2)
      · have hchunk : chooseFixedMatchChunkLen remaining = 257 := by
          simp [chooseFixedMatchChunkLen, hgt, hr1, hr2]
        omega
      · have hchunk : chooseFixedMatchChunkLen remaining = 258 := by
          simp [chooseFixedMatchChunkLen, hgt, hr1, hr2]
        omega
  · have hchunk : chooseFixedMatchChunkLen remaining = remaining := by
      simp [chooseFixedMatchChunkLen, hgt]
    omega

def deflateFixedAuxFast (data : Array UInt8) (i : Nat) (bw : BitWriter) : BitWriter :=
  if h : i < data.size then
    let b := data[i]
    let (bits, len) := fixedLitLenRevCodeFast b.toNat
    deflateFixedAuxFast data (i + 1) (bw.writeBitsFast bits len)
  else
    bw
termination_by data.size - i
decreasing_by
  have hlt : i < data.size := h
  have hle : data.size - (i + 1) < data.size - i := by
    exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
  exact hle

def deflateFixedQuadAuxFast (data : Array UInt8) (i : Nat) (bw : BitWriter) : BitWriter :=
  if h : i < data.size then
    let b := data[i]
    if h3 : i + 3 < data.size then
      if quadTailEqbFast data i b h3 then
        let bw := bw.writeFixedLiteralFast b
        let bw := bw.writeFixedMatchDist1Fast 3
        deflateFixedQuadAuxFast data (i + 4) bw
      else
        deflateFixedQuadAuxFast data (i + 1) (bw.writeFixedLiteralFast b)
    else
      deflateFixedQuadAuxFast data (i + 1) (bw.writeFixedLiteralFast b)
  else
    bw
termination_by data.size - i
decreasing_by
  · have hle : data.size - (i + 4) < data.size - i := by
      omega
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle
  · have hlt : i < data.size := h
    have hle : data.size - (i + 1) < data.size - i := by
      exact Nat.sub_lt_sub_left (k := i) (m := data.size) (n := i + 1) hlt (Nat.lt_succ_self i)
    exact hle

def deflateFixedRunAuxFast (data : Array UInt8) (i : Nat) (bw : BitWriter) : BitWriter :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEndFast data b (i + 1)
    let runLen := j - i
    if h4 : 4 ≤ runLen then
      let bw := bw.writeFixedLiteralFast b
      let bw := bw.writeFixedMatchDist1ChunksFast (runLen - 1)
      deflateFixedRunAuxFast data j bw
    else
      let bw := bw.writeFixedLiteralRepeatFast b runLen
      deflateFixedRunAuxFast data j bw
  else
    bw
termination_by data.size - i
decreasing_by
  ·
    have hlt : i < data.size := h
    let j := sameByteRunEndFast data data[i] (i + 1)
    have hge : i + 1 ≤ j := by
      dsimp [j]
      have hk :
          ∀ k, ∀ j0, data.size - j0 = k →
            j0 ≤ sameByteRunEndFast data data[i] j0 := by
        intro k
        induction k with
        | zero =>
            intro j0 hk
            have hle : data.size ≤ j0 := Nat.le_of_sub_eq_zero hk
            have hlt0 : ¬ j0 < data.size := not_lt_of_ge hle
            simp [sameByteRunEndFast, hlt0]
        | succ k ih =>
            intro j0 hk
            rw [sameByteRunEndFast.eq_def]
            by_cases hlt0 : j0 < data.size
            · by_cases heq : data[j0]'hlt0 = data[i]
              · simp [hlt0, heq]
                have hk' : data.size - (j0 + 1) = k := by omega
                have hrec := ih (j0 + 1) hk'
                omega
              · simp [hlt0, heq]
            · simp [hlt0]
      have hrun := hk (data.size - (i + 1)) (i + 1) rfl
      simpa [j] using hrun
    have hle : j ≤ data.size := by
      dsimp [j]
      have hk :
          ∀ k, ∀ j0, data.size - j0 = k →
            j0 ≤ data.size →
            sameByteRunEndFast data data[i] j0 ≤ data.size := by
        intro k
        induction k with
        | zero =>
            intro j0 hk hj0
            have hle0 : data.size ≤ j0 := Nat.le_of_sub_eq_zero hk
            have hlt0 : ¬ j0 < data.size := not_lt_of_ge hle0
            simpa [sameByteRunEndFast, hlt0] using hj0
        | succ k ih =>
            intro j0 hk hj0
            rw [sameByteRunEndFast.eq_def]
            by_cases hlt0 : j0 < data.size
            · by_cases heq : data[j0]'hlt0 = data[i]
              · simp [hlt0, heq]
                have hk' : data.size - (j0 + 1) = k := by omega
                exact ih (j0 + 1) hk' (Nat.succ_le_of_lt hlt0)
              · simp [hlt0, heq]
                omega
            · simp [hlt0]
              exact hj0
      have hrun := hk (data.size - (i + 1)) (i + 1) rfl (Nat.succ_le_of_lt hlt)
      simpa [j] using hrun
    omega
  ·
    have hlt : i < data.size := h
    let j := sameByteRunEndFast data data[i] (i + 1)
    have hge : i + 1 ≤ j := by
      dsimp [j]
      have hk :
          ∀ k, ∀ j0, data.size - j0 = k →
            j0 ≤ sameByteRunEndFast data data[i] j0 := by
        intro k
        induction k with
        | zero =>
            intro j0 hk
            have hle : data.size ≤ j0 := Nat.le_of_sub_eq_zero hk
            have hlt0 : ¬ j0 < data.size := not_lt_of_ge hle
            simp [sameByteRunEndFast, hlt0]
        | succ k ih =>
            intro j0 hk
            rw [sameByteRunEndFast.eq_def]
            by_cases hlt0 : j0 < data.size
            · by_cases heq : data[j0]'hlt0 = data[i]
              · simp [hlt0, heq]
                have hk' : data.size - (j0 + 1) = k := by omega
                have hrec := ih (j0 + 1) hk'
                omega
              · simp [hlt0, heq]
            · simp [hlt0]
      have hrun := hk (data.size - (i + 1)) (i + 1) rfl
      simpa [j] using hrun
    have hle : j ≤ data.size := by
      dsimp [j]
      have hk :
          ∀ k, ∀ j0, data.size - j0 = k →
            j0 ≤ data.size →
            sameByteRunEndFast data data[i] j0 ≤ data.size := by
        intro k
        induction k with
        | zero =>
            intro j0 hk hj0
            have hle0 : data.size ≤ j0 := Nat.le_of_sub_eq_zero hk
            have hlt0 : ¬ j0 < data.size := not_lt_of_ge hle0
            simpa [sameByteRunEndFast, hlt0] using hj0
        | succ k ih =>
            intro j0 hk hj0
            rw [sameByteRunEndFast.eq_def]
            by_cases hlt0 : j0 < data.size
            · by_cases heq : data[j0]'hlt0 = data[i]
              · simp [hlt0, heq]
                have hk' : data.size - (j0 + 1) = k := by omega
                exact ih (j0 + 1) hk' (Nat.succ_le_of_lt hlt0)
              · simp [hlt0, heq]
                omega
            · simp [hlt0]
              exact hj0
      have hrun := hk (data.size - (i + 1)) (i + 1) rfl (Nat.succ_le_of_lt hlt)
      simpa [j] using hrun
    omega

-- Candidate follow-up encoder that emits length/distance matches for repeated bytes.
def deflateFixedMatchFast (raw : ByteArray) : ByteArray :=
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 1 2
  let bw3 := Id.run do
    let data := raw.data
    let mut i : Nat := 0
    let mut bw := bw2
    while i < data.size do
      let b := data[i]!
      let mut j := i + 1
      let mut scanning := true
      while scanning do
        if j < data.size then
          if data[j]! == b then
            j := j + 1
          else
            scanning := false
        else
          scanning := false
      let runLen := j - i
      if runLen >= 4 then
        bw := bw.writeFixedLiteralFast b
        let mut remaining := runLen - 1
        while remaining >= 3 do
          let chunk := chooseFixedMatchChunkLen remaining
          bw := bw.writeFixedMatchDist1Fast chunk
          remaining := remaining - chunk
        while remaining > 0 do
          bw := bw.writeFixedLiteralFast b
          remaining := remaining - 1
      else
        let mut k : Nat := 0
        while k < runLen do
          bw := bw.writeFixedLiteralFast b
          k := k + 1
      i := j
    return bw
  let (eobBits, eobLen) := fixedLitLenRevCodeFast 256
  let bw4 := bw3.writeBits eobBits eobLen
  bw4.flush

def deflateFixedSpec (raw : ByteArray) : ByteArray :=
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 1 2
  let bw3 := deflateFixedAux raw.data 0 bw2
  let (eobCode, eobLen) := fixedLitLenCode 256
  let bw4 := bw3.writeBits (reverseBits eobCode eobLen) eobLen
  bw4.flush

def deflateFixedFast (raw : ByteArray) : ByteArray :=
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 1 2
  let bw3 := deflateFixedAuxFast raw.data 0 bw2
  let (eobCode, eobLen) := fixedLitLenCode 256
  let bw4 := bw3.writeBits (reverseBits eobCode eobLen) eobLen
  bw4.flush

def deflateFixedQuadFast (raw : ByteArray) : ByteArray :=
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 1 2
  let bw3 := deflateFixedQuadAuxFast raw.data 0 bw2
  let (eobCode, eobLen) := fixedLitLenCode 256
  let bw4 := bw3.writeBits (reverseBits eobCode eobLen) eobLen
  bw4.flush

def deflateFixedRunFast (raw : ByteArray) : ByteArray :=
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 1 2
  let bw3 := deflateFixedRunAuxFast raw.data 0 bw2
  let (eobCode, eobLen) := fixedLitLenCode 256
  let bw4 := bw3.writeBits (reverseBits eobCode eobLen) eobLen
  bw4.flush

inductive Lz77Token where
  | literal (b : UInt8)
  | match (len distance : Nat)
deriving Repr, DecidableEq

def lz77EmptyBuckets : Array (Array Nat) :=
  Array.replicate deflateHashBucketCount #[]

@[inline] def lz77HashAt (data : Array UInt8) (i : Nat) : Nat :=
  if i + 2 < data.size then
    (((data[i]!.toNat * 257 + data[i + 1]!.toNat) * 257 + data[i + 2]!.toNat) %
      deflateHashBucketCount)
  else
    0

@[inline] def lz77InsertPosition (data : Array UInt8) (buckets : Array (Array Nat))
    (pos : Nat) : Array (Array Nat) :=
  if pos + 2 < data.size then
    let hash := lz77HashAt data pos
    let bucket := buckets[hash]!
    buckets.set! hash (bucket.push pos)
  else
    buckets

def lz77InsertPositions (data : Array UInt8) (stop pos : Nat)
    (buckets : Array (Array Nat)) : Array (Array Nat) :=
  if h : pos < stop then
    lz77InsertPositions data stop (pos + 1) (lz77InsertPosition data buckets pos)
  else
    buckets
termination_by stop - pos
decreasing_by
  exact Nat.sub_lt_sub_left (k := pos) (m := stop) (n := pos + 1) h (Nat.lt_succ_self pos)

def lz77CommonLenAux (data : Array UInt8) (i candidate maxLen len : Nat) : Nat :=
  if h : len < maxLen then
    if data[i + len]! == data[candidate + len]! then
      lz77CommonLenAux data i candidate maxLen (len + 1)
    else
      len
  else
    len
termination_by maxLen - len
decreasing_by
  exact Nat.sub_lt_sub_left (k := len) (m := maxLen) (n := len + 1) h (Nat.lt_succ_self len)

@[inline] def lz77CommonLen (data : Array UInt8) (i candidate maxLen : Nat) : Nat :=
  lz77CommonLenAux data i candidate maxLen 0

@[inline] def lz77BetterMatch (bestLen bestDistance len distance : Nat) : Bool :=
  len > bestLen || (len == bestLen && (bestDistance == 0 || distance < bestDistance))

def lz77FindBestInBucket (data : Array UInt8) (i : Nat) (bucket : Array Nat)
    (revIdx bestLen bestDistance : Nat) : Option (Nat × Nat) :=
  if 0 < revIdx then
    let candidate := bucket[revIdx - 1]!
    let (bestLen, bestDistance) :=
      if candidate < i then
        let distance := i - candidate
        if distance ≤ deflateMaxDistance then
          let maxLen := Nat.min deflateMaxMatchLen (data.size - i)
          let len := lz77CommonLen data i candidate maxLen
          if deflateMinMatchLen ≤ len && lz77BetterMatch bestLen bestDistance len distance then
            (len, distance)
          else
            (bestLen, bestDistance)
        else
          (bestLen, bestDistance)
      else
        (bestLen, bestDistance)
    if bestLen == deflateMaxMatchLen then
      some (bestLen, bestDistance)
    else
      lz77FindBestInBucket data i bucket (revIdx - 1) bestLen bestDistance
  else if deflateMinMatchLen ≤ bestLen then
    some (bestLen, bestDistance)
  else
    none
termination_by revIdx
decreasing_by
  omega

@[inline] def lz77FindBest (data : Array UInt8) (i : Nat)
    (buckets : Array (Array Nat)) : Option (Nat × Nat) :=
  if i + 2 < data.size then
    let bucket := buckets[lz77HashAt data i]!
    lz77FindBestInBucket data i bucket bucket.size 0 0
  else
    none

def deflateTokensLz77Aux (fuel : Nat) (data : Array UInt8) (i : Nat)
    (buckets : Array (Array Nat)) (tokens : Array Lz77Token) : Array Lz77Token :=
  match fuel with
  | 0 => tokens
  | fuel + 1 =>
      if _h : i < data.size then
        match lz77FindBest data i buckets with
        | some (len, distance) =>
            let j := Nat.min data.size (i + len)
            let buckets := lz77InsertPositions data j i buckets
            deflateTokensLz77Aux fuel data j buckets (tokens.push (.match len distance))
        | none =>
            let buckets := lz77InsertPositions data (i + 1) i buckets
            deflateTokensLz77Aux fuel data (i + 1) buckets (tokens.push (.literal data[i]))
      else
        tokens

def deflateTokensLz77 (raw : ByteArray) : Array Lz77Token :=
  deflateTokensLz77Aux raw.size raw.data 0 lz77EmptyBuckets #[]

def lz77CopyDistanceFast (out : ByteArray) (distance len : Nat) : Option ByteArray :=
  if distance = 0 || distance > out.size then
    none
  else
    some <| Id.run do
      let mut result := out
      for _ in [0:len] do
        let idx := result.size - distance
        let b := result.get! idx
        result := result.push b
      return result

def lz77TokenExpand? (out : ByteArray) : Lz77Token → Option ByteArray
  | .literal b => some (out.push b)
  | .match len distance =>
      if deflateMinMatchLen ≤ len && len ≤ deflateMaxMatchLen &&
          1 ≤ distance && distance ≤ deflateMaxDistance then
        lz77CopyDistanceFast out distance len
      else
        none

def deflateTokensExpandLz77From? (tokens : Array Lz77Token) (i : Nat)
    (out : ByteArray) : Option ByteArray :=
  if h : i < tokens.size then
    match lz77TokenExpand? out tokens[i] with
    | some out' => deflateTokensExpandLz77From? tokens (i + 1) out'
    | none => none
  else
    some out
termination_by tokens.size - i
decreasing_by
  exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1) h
    (Nat.lt_succ_self i)

def deflateTokensExpandLz77? (tokens : Array Lz77Token) : Option ByteArray :=
  deflateTokensExpandLz77From? tokens 0 ByteArray.empty

def writeFixedPayloadLz77From (bw : BitWriter) (tokens : Array Lz77Token) (i : Nat) :
    BitWriter :=
  if h : i < tokens.size then
    let bw :=
      match tokens[i] with
      | .literal b => bw.writeFixedLiteralFast b
      | .match len distance => bw.writeFixedMatchFast len distance
    writeFixedPayloadLz77From bw tokens (i + 1)
  else
    bw
termination_by tokens.size - i
decreasing_by
  exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1) h
    (Nat.lt_succ_self i)

def writeFixedPayloadLz77 (bw : BitWriter) (tokens : Array Lz77Token) : BitWriter :=
  writeFixedPayloadLz77From bw tokens 0

def deflateFixedLz77 (raw : ByteArray) : ByteArray :=
  let tokens := deflateTokensLz77 raw
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 1 2
  let bw3 := writeFixedPayloadLz77 bw2 tokens
  let (eobCode, eobLen) := fixedLitLenCode 256
  let bw4 := bw3.writeBits (reverseBits eobCode eobLen) eobLen
  bw4.flush

def deflateFixed (raw : ByteArray) : ByteArray :=
  deflateFixedLz77 raw

inductive DeflateToken where
  | literal (b : UInt8)
  | matchDist1 (len : Nat)
deriving Repr, DecidableEq

def deflateMatchDist1Chunks (tokens : Array DeflateToken) (remaining : Nat) :
    Array DeflateToken :=
  if _h : 3 ≤ remaining then
    let chunk := chooseFixedMatchChunkLen remaining
    deflateMatchDist1Chunks (tokens.push (.matchDist1 chunk)) (remaining - chunk)
  else
    tokens
termination_by remaining
decreasing_by
  by_cases hgt : remaining > 258
  · by_cases hr1 : (remaining % 258 == 1)
    · have hchunk : chooseFixedMatchChunkLen remaining = 256 := by
        simp [chooseFixedMatchChunkLen, hgt, hr1]
      omega
    · by_cases hr2 : (remaining % 258 == 2)
      · have hchunk : chooseFixedMatchChunkLen remaining = 257 := by
          simp [chooseFixedMatchChunkLen, hgt, hr1, hr2]
        omega
      · have hchunk : chooseFixedMatchChunkLen remaining = 258 := by
          simp [chooseFixedMatchChunkLen, hgt, hr1, hr2]
        omega
  · have hchunk : chooseFixedMatchChunkLen remaining = remaining := by
      simp [chooseFixedMatchChunkLen, hgt]
    omega

def pushLiteralRepeat (tokens : Array DeflateToken) (b : UInt8) : Nat → Array DeflateToken
  | 0 => tokens
  | n + 1 => pushLiteralRepeat (tokens.push (.literal b)) b n

def deflateTokensDist1Aux (data : Array UInt8) (i : Nat) (tokens : Array DeflateToken) :
    Array DeflateToken :=
  if h : i < data.size then
    let b := data[i]
    let j := sameByteRunEndFast data b (i + 1)
    let runLen := j - i
    let tokens :=
      if _h4 : 4 ≤ runLen then
        deflateMatchDist1Chunks (tokens.push (.literal b)) (runLen - 1)
      else
        pushLiteralRepeat tokens b runLen
    deflateTokensDist1Aux data j tokens
  else
    tokens
termination_by data.size - i
decreasing_by
  ·
    have hlt : i < data.size := h
    let j := sameByteRunEndFast data data[i] (i + 1)
    have hge : i + 1 ≤ j := by
      dsimp [j]
      have hk :
          ∀ k, ∀ j0, data.size - j0 = k →
            j0 ≤ sameByteRunEndFast data data[i] j0 := by
        intro k
        induction k with
        | zero =>
            intro j0 hk
            have hle : data.size ≤ j0 := Nat.le_of_sub_eq_zero hk
            have hlt0 : ¬ j0 < data.size := not_lt_of_ge hle
            simp [sameByteRunEndFast, hlt0]
        | succ k ih =>
            intro j0 hk
            rw [sameByteRunEndFast.eq_def]
            by_cases hlt0 : j0 < data.size
            · by_cases heq : data[j0]'hlt0 = data[i]
              · simp [hlt0, heq]
                have hk' : data.size - (j0 + 1) = k := by omega
                have hrec := ih (j0 + 1) hk'
                omega
              · simp [hlt0, heq]
            · simp [hlt0]
      have hrun := hk (data.size - (i + 1)) (i + 1) rfl
      simpa [j] using hrun
    have hle : j ≤ data.size := by
      dsimp [j]
      have hk :
          ∀ k, ∀ j0, data.size - j0 = k →
            j0 ≤ data.size →
            sameByteRunEndFast data data[i] j0 ≤ data.size := by
        intro k
        induction k with
        | zero =>
            intro j0 hk hj0
            have hle0 : data.size ≤ j0 := Nat.le_of_sub_eq_zero hk
            have hlt0 : ¬ j0 < data.size := not_lt_of_ge hle0
            simpa [sameByteRunEndFast, hlt0] using hj0
        | succ k ih =>
            intro j0 hk hj0
            rw [sameByteRunEndFast.eq_def]
            by_cases hlt0 : j0 < data.size
            · by_cases heq : data[j0]'hlt0 = data[i]
              · simp [hlt0, heq]
                have hk' : data.size - (j0 + 1) = k := by omega
                exact ih (j0 + 1) hk' (Nat.succ_le_of_lt hlt0)
              · simp [hlt0, heq]
                omega
            · simp [hlt0]
              exact hj0
      have hrun := hk (data.size - (i + 1)) (i + 1) rfl (Nat.succ_le_of_lt hlt)
      simpa [j] using hrun
    omega

def deflateTokensDist1 (raw : ByteArray) : Array DeflateToken :=
  deflateTokensDist1Aux raw.data 0 #[]

def pushByteRepeat (out : ByteArray) (b : UInt8) : Nat → ByteArray
  | 0 => out
  | n + 1 => pushByteRepeat (out.push b) b n

def deflateTokenExpand (out : ByteArray) : DeflateToken → ByteArray
  | .literal b => out.push b
  | .matchDist1 len =>
      if out.size == 0 then
        out
      else
        let b := out.get! (out.size - 1)
        pushByteRepeat out b len

def deflateTokensExpand (tokens : Array DeflateToken) : ByteArray :=
  tokens.foldl deflateTokenExpand ByteArray.empty

def deflateTokensHasMatchDist1Aux (tokens : Array DeflateToken) (i : Nat) : Bool :=
  if h : i < tokens.size then
    match tokens[i] with
    | .literal _ => deflateTokensHasMatchDist1Aux tokens (i + 1)
    | .matchDist1 _ => true
  else
    false
termination_by tokens.size - i
decreasing_by
  have hlt : i < tokens.size := h
  exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1) hlt (Nat.lt_succ_self i)

def deflateTokensHasMatchDist1 (tokens : Array DeflateToken) : Bool :=
  deflateTokensHasMatchDist1Aux tokens 0

def incrementNatAt (arr : Array Nat) (idx : Nat) : Array Nat :=
  arr.set! idx (arr[idx]! + 1)

def litLenSymbolFreqsAux (tokens : Array DeflateToken) (i : Nat)
    (freqs : Array Nat) : Array Nat :=
  if h : i < tokens.size then
    let freqs :=
      match tokens[i] with
      | .literal b => incrementNatAt freqs b.toNat
      | .matchDist1 len =>
          let (sym, _, _) := fixedLenMatchInfo len
          incrementNatAt freqs sym
    litLenSymbolFreqsAux tokens (i + 1) freqs
  else
    freqs
termination_by tokens.size - i
decreasing_by
  have hlt : i < tokens.size := h
  exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1) hlt (Nat.lt_succ_self i)

def litLenSymbolFreqs (tokens : Array DeflateToken) : Array Nat :=
  incrementNatAt (litLenSymbolFreqsAux tokens 0 (Array.replicate 286 0)) 256

def distSymbolFreqsAux (tokens : Array DeflateToken) (i : Nat)
    (freqs : Array Nat) : Array Nat :=
  if h : i < tokens.size then
    let freqs :=
      match tokens[i] with
      | .literal _ => freqs
      | .matchDist1 _ => incrementNatAt freqs 0
    distSymbolFreqsAux tokens (i + 1) freqs
  else
    freqs
termination_by tokens.size - i
decreasing_by
  have hlt : i < tokens.size := h
  exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1) hlt (Nat.lt_succ_self i)

def distSymbolFreqs (tokens : Array DeflateToken) : Array Nat :=
  distSymbolFreqsAux tokens 0 (Array.replicate 30 0)

def litLenSymbolFreqsLz77Aux (tokens : Array Lz77Token) (i : Nat)
    (freqs : Array Nat) : Array Nat :=
  if h : i < tokens.size then
    let freqs :=
      match tokens[i] with
      | .literal b => incrementNatAt freqs b.toNat
      | .match len _distance =>
          let (sym, _, _) := deflateLengthInfo len
          incrementNatAt freqs sym
    litLenSymbolFreqsLz77Aux tokens (i + 1) freqs
  else
    freqs
termination_by tokens.size - i
decreasing_by
  exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1) h
    (Nat.lt_succ_self i)

def litLenSymbolFreqsLz77 (tokens : Array Lz77Token) : Array Nat :=
  incrementNatAt (litLenSymbolFreqsLz77Aux tokens 0 (Array.replicate 286 0)) 256

def distSymbolFreqsLz77Aux (tokens : Array Lz77Token) (i : Nat)
    (freqs : Array Nat) : Array Nat :=
  if h : i < tokens.size then
    let freqs :=
      match tokens[i] with
      | .literal _ => freqs
      | .match _len distance =>
          match deflateDistanceInfo? distance with
          | some (sym, _, _) => incrementNatAt freqs sym
          | none => freqs
    distSymbolFreqsLz77Aux tokens (i + 1) freqs
  else
    freqs
termination_by tokens.size - i
decreasing_by
  exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1) h
    (Nat.lt_succ_self i)

def distSymbolFreqsLz77 (tokens : Array Lz77Token) : Array Nat :=
  distSymbolFreqsLz77Aux tokens 0 (Array.replicate 30 0)

/-- Uniform code length for generated dynamic literal/length alphabets.
The literal/length alphabet has at most 286 symbols, so 9 bits leaves room for
a complete canonical table while still omitting unused symbols. -/
def generatedDynamicLitLenCodeLen : Nat := 9

def generatedDynamicLitLenLengthAt (freqs : Array Nat) (idx : Nat) : Nat :=
  if freqs[idx]! > 0 then
    generatedDynamicLitLenCodeLen
  else
    0

def generatedDynamicLitLenLengths (freqs : Array Nat) : Array Nat :=
  Array.ofFn (fun idx : Fin freqs.size => generatedDynamicLitLenLengthAt freqs idx.val)

def generatedDynamicDistLengthAt (freqs : Array Nat) (idx : Nat) : Nat :=
  if idx == 0 && freqs[0]! > 0 then
    1
  else
    0

def generatedDynamicDistLengths (freqs : Array Nat) : Array Nat :=
  Array.ofFn (fun idx : Fin freqs.size => generatedDynamicDistLengthAt freqs idx.val)

def generatedDynamicDistLengthsLz77 (_freqs : Array Nat) : Array Nat :=
  Array.replicate 30 5

def lastNonZeroIndex (arr : Array Nat) (minIdx : Nat) : Nat :=
  Id.run do
    let mut last := minIdx
    for i in [0:arr.size] do
      if arr[i]! > 0 then
        last := i
    return last

def maxCodeLenAux (lengths : Array Nat) (i maxLen : Nat) : Nat :=
  if h : i < lengths.size then
    let len := lengths[i]
    let maxLen := if len > maxLen then len else maxLen
    maxCodeLenAux lengths (i + 1) maxLen
  else
    maxLen
termination_by lengths.size - i
decreasing_by
  have hlt : i < lengths.size := h
  exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1) hlt (Nat.lt_succ_self i)

def countCodeLengthsAux (lengths : Array Nat) (i : Nat) (count : Array Nat) :
    Array Nat :=
  if h : i < lengths.size then
    let len := lengths[i]
    let count :=
      if len > 0 then
        incrementNatAt count len
      else
        count
    countCodeLengthsAux lengths (i + 1) count
  else
    count
termination_by lengths.size - i
decreasing_by
  have hlt : i < lengths.size := h
  exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1) hlt (Nat.lt_succ_self i)

def nextCodesAux (count : Array Nat) (maxLen bits code : Nat) (nextCode : Array Nat) :
    Nat × Array Nat :=
  if h : bits < maxLen + 1 then
    let code := (code + count[bits - 1]!) <<< 1
    let nextCode := nextCode.set! bits code
    nextCodesAux count maxLen (bits + 1) code nextCode
  else
    (code, nextCode)
termination_by maxLen + 1 - bits
decreasing_by
  have hlt : bits < maxLen + 1 := h
  exact Nat.sub_lt_sub_left (k := bits) (m := maxLen + 1) (n := bits + 1)
    hlt (Nat.lt_succ_self bits)

def fillCanonicalRevCodesAux (lengths : Array Nat) (i : Nat)
    (nextCode : Array Nat) (revCodes : Array (Nat × Nat)) : Array (Nat × Nat) :=
  if h : i < lengths.size then
    let len := lengths[i]
    let (nextCode, revCodes) :=
      if len > 0 then
        let codeVal := nextCode[len]!
        let nextCode := nextCode.set! len (codeVal + 1)
        let revCodes := revCodes.set! i (reverseBits codeVal len, len)
        (nextCode, revCodes)
      else
        (nextCode, revCodes)
    fillCanonicalRevCodesAux lengths (i + 1) nextCode revCodes
  else
    revCodes
termination_by lengths.size - i
decreasing_by
  have hlt : i < lengths.size := h
  exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1) hlt (Nat.lt_succ_self i)

def canonicalRevCodesFromLengths (lengths : Array Nat) : Array (Nat × Nat) :=
  let maxLen := maxCodeLenAux lengths 0 0
  let count := countCodeLengthsAux lengths 0 (Array.replicate (maxLen + 1) 0)
  let nextCode0 : Array Nat := Array.replicate (maxLen + 1) 0
  let (_, nextCode) := nextCodesAux count maxLen 1 0 nextCode0
  let revCodes : Array (Nat × Nat) := Array.replicate lengths.size (0, 0)
  fillCanonicalRevCodesAux lengths 0 nextCode revCodes

def codeLenCodeLengths : Array Nat :=
  Array.replicate 19 5

def codeLenOrder : Array Nat :=
  #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

def generatedCodeLenCodeLengthsBits : Nat :=
  Id.run do
    let mut bits := 0
    let mut shift := 0
    for i in [0:codeLenOrder.size] do
      bits := bits ||| (codeLenCodeLengths[codeLenOrder[i]!]! <<< shift)
      shift := shift + 3
    return bits

def generatedDynamicHeaderPrefixBits (litLenCount distCount : Nat) : Nat :=
  (litLenCount - 257) |||
    ((distCount - 1) <<< 5) |||
    (15 <<< 10) |||
    (generatedCodeLenCodeLengthsBits <<< 14)

def generatedDynamicHeaderPrefixLen : Nat :=
  14 + codeLenOrder.size * 3

@[inline] def BitWriter.writeRevCode (bw : BitWriter) (codes : Array (Nat × Nat)) (sym : Nat) :
    BitWriter :=
  let (bits, len) := codes[sym]!
  bw.writeBitsFast bits len

def BitWriter.writeCodeLenSymbol (bw : BitWriter) (codeLenCodes : Array (Nat × Nat))
    (sym : Nat) : BitWriter :=
  bw.writeRevCode codeLenCodes sym

def BitWriter.writeCodeLenRepeat (bw : BitWriter) (codeLenCodes : Array (Nat × Nat))
    (sym extra extraLen : Nat) : BitWriter :=
  let bw := bw.writeCodeLenSymbol codeLenCodes sym
  bw.writeBitsFast extra extraLen

inductive CodeLenToken where
  | literal (len : Nat)
  | repeatPrev (repeatCount : Nat)
  | repeatZeroShort (repeatCount : Nat)
  | repeatZeroLong (repeatCount : Nat)
deriving Repr, DecidableEq

def pushNatRepeat (xs : Array Nat) (value : Nat) : Nat → Array Nat
  | 0 => xs
  | n + 1 => pushNatRepeat (xs.push value) value n

def CodeLenToken.symbol : CodeLenToken → Nat
  | .literal len => len
  | .repeatPrev _ => 16
  | .repeatZeroShort _ => 17
  | .repeatZeroLong _ => 18

def CodeLenToken.extraBits : CodeLenToken → Nat
  | .literal _ => 0
  | .repeatPrev repeatCount => repeatCount - 3
  | .repeatZeroShort repeatCount => repeatCount - 3
  | .repeatZeroLong repeatCount => repeatCount - 11

def CodeLenToken.extraLen : CodeLenToken → Nat
  | .literal _ => 0
  | .repeatPrev _ => 2
  | .repeatZeroShort _ => 3
  | .repeatZeroLong _ => 7

def CodeLenToken.expand (lengths : Array Nat) : CodeLenToken → Option (Array Nat)
  | .literal len => some (lengths.push len)
  | .repeatPrev repeatCount =>
      if _h : lengths.size == 0 then
        none
      else
        let prev := lengths[lengths.size - 1]!
        some (pushNatRepeat lengths prev repeatCount)
  | .repeatZeroShort repeatCount => some (pushNatRepeat lengths 0 repeatCount)
  | .repeatZeroLong repeatCount => some (pushNatRepeat lengths 0 repeatCount)

def codeLenTokensExpandAux? (tokens : Array CodeLenToken) (i : Nat)
    (lengths : Array Nat) : Option (Array Nat) :=
  if h : i < tokens.size then
    match tokens[i].expand lengths with
    | none => none
    | some lengths => codeLenTokensExpandAux? tokens (i + 1) lengths
  else
    some lengths
termination_by tokens.size - i
decreasing_by
  have hlt : i < tokens.size := h
  exact Nat.sub_lt_sub_left (k := i) (m := tokens.size) (n := i + 1)
    hlt (Nat.lt_succ_self i)

def codeLenTokensExpand? (tokens : Array CodeLenToken) : Option (Array Nat) :=
  codeLenTokensExpandAux? tokens 0 #[]

def BitWriter.writeCodeLenToken (bw : BitWriter) (codeLenCodes : Array (Nat × Nat))
    (token : CodeLenToken) : BitWriter :=
  let bw := bw.writeCodeLenSymbol codeLenCodes token.symbol
  bw.writeBitsFast token.extraBits token.extraLen

def BitWriter.writeCodeLenTokens (bw : BitWriter) (codeLenCodes : Array (Nat × Nat))
    (tokens : Array CodeLenToken) : BitWriter :=
  Id.run do
    let mut bw := bw
    for token in tokens do
      bw := bw.writeCodeLenToken codeLenCodes token
    return bw

def codeLenZeroRunTokensAux (tokens : Array CodeLenToken) (runLen : Nat) :
    Array CodeLenToken :=
  if _h18 : 11 ≤ runLen then
    let chunk := Nat.min 138 runLen
    codeLenZeroRunTokensAux (tokens.push (.repeatZeroLong chunk)) (runLen - chunk)
  else if _h17 : 3 ≤ runLen then
    let chunk := Nat.min 10 runLen
    codeLenZeroRunTokensAux (tokens.push (.repeatZeroShort chunk)) (runLen - chunk)
  else
    Id.run do
      let mut tokens := tokens
      for _ in [0:runLen] do
        tokens := tokens.push (.literal 0)
      return tokens
termination_by runLen
decreasing_by
  · have hpos : 0 < Nat.min 138 runLen := by
      rw [Nat.lt_min]
      exact ⟨by decide, by omega⟩
    have hle : Nat.min 138 runLen ≤ runLen := Nat.min_le_right 138 runLen
    exact Nat.sub_lt_self hpos hle
  · have hpos : 0 < Nat.min 10 runLen := by
      rw [Nat.lt_min]
      exact ⟨by decide, by omega⟩
    have hle : Nat.min 10 runLen ≤ runLen := Nat.min_le_right 10 runLen
    exact Nat.sub_lt_self hpos hle

def codeLenZeroRunTokens (runLen : Nat) : Array CodeLenToken :=
  codeLenZeroRunTokensAux #[] runLen

def codeLenNonzeroRunTokensAux (tokens : Array CodeLenToken) (len runLen : Nat) :
    Array CodeLenToken :=
  if h16 : 4 ≤ runLen then
    let repeatCount := Nat.min 6 (runLen - 1)
    let tokens := tokens.push (.literal len)
    let tokens := tokens.push (.repeatPrev repeatCount)
    codeLenNonzeroRunTokensAux tokens len (runLen - (1 + repeatCount))
  else
    Id.run do
      let mut tokens := tokens
      for _ in [0:runLen] do
        tokens := tokens.push (.literal len)
      return tokens
termination_by runLen
decreasing_by
  have hrepPos : 0 < Nat.min 6 (runLen - 1) := by
    rw [Nat.lt_min]
    exact ⟨by decide, by omega⟩
  have hrepLe : Nat.min 6 (runLen - 1) ≤ runLen - 1 := Nat.min_le_right 6 (runLen - 1)
  have : 1 + Nat.min 6 (runLen - 1) ≤ runLen := by omega
  omega

def codeLenNonzeroRunTokens (len runLen : Nat) : Array CodeLenToken :=
  codeLenNonzeroRunTokensAux #[] len runLen

def BitWriter.writeZeroCodeLenRun (bw : BitWriter) (codeLenCodes : Array (Nat × Nat))
    (runLen : Nat) : BitWriter :=
  bw.writeCodeLenTokens codeLenCodes (codeLenZeroRunTokens runLen)

def BitWriter.writeNonzeroCodeLenRun (bw : BitWriter) (codeLenCodes : Array (Nat × Nat))
    (len runLen : Nat) : BitWriter :=
  bw.writeCodeLenTokens codeLenCodes (codeLenNonzeroRunTokens len runLen)

def codeLenRunEnd (lengths : Array Nat) (i : Nat) : Nat :=
  if h : i < lengths.size then
    Id.run do
      let len := lengths[i]
      let mut j := i + 1
      let mut running := true
      while running do
        if hj : j < lengths.size then
          if lengths[j] == len then
            j := j + 1
          else
            running := false
        else
          running := false
      return j
  else
    i

def codeLenTokensOfLengthsAux (lengths : Array Nat)
    (tokens : Array CodeLenToken) (i fuel : Nat) : Array CodeLenToken :=
  match fuel with
  | 0 => tokens
  | fuel + 1 =>
      if h : i < lengths.size then
        let j := codeLenRunEnd lengths i
        let len := lengths[i]
        let runLen := j - i
        let tokens :=
          if len == 0 then
            codeLenZeroRunTokensAux tokens runLen
          else
            codeLenNonzeroRunTokensAux tokens len runLen
        codeLenTokensOfLengthsAux lengths tokens j fuel
      else
        tokens

def codeLenTokensOfLengths (lengths : Array Nat) : Array CodeLenToken :=
  codeLenTokensOfLengthsAux lengths #[] 0 (lengths.size + 1)

def codeLenLiteralTokensOfLengths (lengths : Array Nat) : Array CodeLenToken :=
  lengths.map CodeLenToken.literal

def BitWriter.writeDynamicCodeLengths (bw : BitWriter) (lengths : Array Nat)
    (codeLenCodes : Array (Nat × Nat)) : BitWriter :=
  bw.writeCodeLenTokens codeLenCodes (codeLenLiteralTokensOfLengths lengths)

def generatedDynamicLitLenCount (_litLenLengths : Array Nat) : Nat :=
  286

def generatedDynamicDistCount (_distLengths : Array Nat) : Nat :=
  30

def writeGeneratedDynamicHeader (bw : BitWriter)
    (litLenLengths distLengths : Array Nat) : BitWriter :=
  let litLenCount := generatedDynamicLitLenCount litLenLengths
  let distCount := generatedDynamicDistCount distLengths
  let codeLenCodes := canonicalRevCodesFromLengths codeLenCodeLengths
  let bw :=
    bw.writeBitsFast
      (generatedDynamicHeaderPrefixBits litLenCount distCount)
      generatedDynamicHeaderPrefixLen
  let lengths := (litLenLengths.extract 0 litLenCount) ++ (distLengths.extract 0 distCount)
  bw.writeDynamicCodeLengths lengths codeLenCodes

def writeDynamicPayload (bw : BitWriter) (tokens : Array DeflateToken)
    (litLenCodes distCodes : Array (Nat × Nat)) : BitWriter :=
  Id.run do
    let mut bw := bw
    for token in tokens do
      match token with
      | .literal b =>
          bw := bw.writeRevCode litLenCodes b.toNat
      | .matchDist1 len =>
          let (sym, extraBits, extraLen) := fixedLenMatchInfo len
          bw := bw.writeRevCode litLenCodes sym
          bw := bw.writeBitsFast extraBits extraLen
          bw := bw.writeRevCode distCodes 0
    bw := bw.writeRevCode litLenCodes 256
    return bw

def writeDynamicPayloadLz77 (bw : BitWriter) (tokens : Array Lz77Token)
    (litLenCodes distCodes : Array (Nat × Nat)) : BitWriter :=
  Id.run do
    let mut bw := bw
    for token in tokens do
      match token with
      | .literal b =>
          bw := bw.writeRevCode litLenCodes b.toNat
      | .match len distance =>
          let (sym, extraBits, extraLen) := deflateLengthInfo len
          bw := bw.writeRevCode litLenCodes sym
          bw := bw.writeBitsFast extraBits extraLen
          match deflateDistanceInfo? distance with
          | some (distSym, distExtraBits, distExtraLen) =>
              bw := bw.writeRevCode distCodes distSym
              bw := bw.writeBitsFast distExtraBits distExtraLen
          | none =>
              bw := bw.writeRevCode distCodes 0
    bw := bw.writeRevCode litLenCodes 256
    return bw

def deflateDynamicFullFast (raw : ByteArray) : ByteArray :=
  let tokens := deflateTokensDist1 raw
  let litLenLengths := generatedDynamicLitLenLengths (litLenSymbolFreqs tokens)
  let distLengths := generatedDynamicDistLengths (distSymbolFreqs tokens)
  let litLenCodes := canonicalRevCodesFromLengths litLenLengths
  let distCodes := canonicalRevCodesFromLengths distLengths
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 2 2
  let bw3 := writeGeneratedDynamicHeader bw2 litLenLengths distLengths
  let bw4 := writeDynamicPayload bw3 tokens litLenCodes distCodes
  bw4.flush

def deflateDynamicLz77 (raw : ByteArray) : ByteArray :=
  let tokens := deflateTokensLz77 raw
  let litLenLengths := generatedDynamicLitLenLengths (litLenSymbolFreqsLz77 tokens)
  let distLengths := generatedDynamicDistLengthsLz77 (distSymbolFreqsLz77 tokens)
  let litLenCodes := canonicalRevCodesFromLengths litLenLengths
  let distCodes := canonicalRevCodesFromLengths distLengths
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 2 2
  let bw3 := writeGeneratedDynamicHeader bw2 litLenLengths distLengths
  let bw4 := writeDynamicPayloadLz77 bw3 tokens litLenCodes distCodes
  bw4.flush

@[inline] def writeDynamicFixedTables (bw : BitWriter) : BitWriter :=
  Id.run do
    let mut bw := bw
    -- Code-length alphabet lengths in deflate order
    -- [16, 17, 18, 0, 8, 7, 9, 6, 10, 5].
    bw := bw.writeBitsFast 0 3
    bw := bw.writeBitsFast 0 3
    bw := bw.writeBitsFast 0 3
    bw := bw.writeBitsFast 0 3
    bw := bw.writeBitsFast 2 3
    bw := bw.writeBitsFast 2 3
    bw := bw.writeBitsFast 2 3
    bw := bw.writeBitsFast 0 3
    bw := bw.writeBitsFast 0 3
    bw := bw.writeBitsFast 2 3
    -- Lit/len lengths for fixed tables, encoded by the dynamic code-length table.
    -- Symbol 8  -> rev(code)=1 (len=2)
    -- Symbol 9  -> rev(code)=3 (len=2)
    -- Symbol 7  -> rev(code)=2 (len=2)
    -- Symbol 5  -> rev(code)=0 (len=2)
    for _ in [0:144] do
      bw := bw.writeBitsFast 1 2
    for _ in [0:112] do
      bw := bw.writeBitsFast 3 2
    for _ in [0:24] do
      bw := bw.writeBitsFast 2 2
    for _ in [0:8] do
      bw := bw.writeBitsFast 1 2
    for _ in [0:32] do
      bw := bw.writeBitsFast 0 2
    return bw

def deflateDynamicFast (raw : ByteArray) : ByteArray :=
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 2 2
  let bw3 := bw2.writeBits 31 5
  let bw4 := bw3.writeBits 31 5
  let bw5 := bw4.writeBits 6 4
  let bw6 := writeDynamicFixedTables bw5
  let bw7 := deflateFixedAuxFast raw.data 0 bw6
  let (eobBits, eobLen) := fixedLitLenRevCodeFast 256
  let bw8 := bw7.writeBitsFast eobBits eobLen
  bw8.flush

def deflateDynamic (raw : ByteArray) : ByteArray :=
  deflateDynamicLz77 raw

def zlibCompressFixed (raw : ByteArray) : ByteArray :=
  let header := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateFixed raw
  let adler := u32be (adler32 raw).toNat
  let outSize := header.size + deflated.size + adler.size
  let out := ByteArray.emptyWithCapacity outSize
  out ++ header ++ deflated ++ adler


def zlibCompressStored (raw : ByteArray) : ByteArray :=
  let header := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateStored raw
  let adler := u32be (adler32 raw).toNat
  let outSize := header.size + deflated.size + adler.size
  let out := ByteArray.emptyWithCapacity outSize
  out ++ header ++ deflated ++ adler

def zlibCompressDynamic (raw : ByteArray) : ByteArray :=
  let header := ByteArray.mk #[u8 0x78, u8 0x01]
  let deflated := deflateDynamic raw
  let adler := u32be (adler32 raw).toNat
  let outSize := header.size + deflated.size + adler.size
  let out := ByteArray.emptyWithCapacity outSize
  out ++ header ++ deflated ++ adler

structure BitReader where
  data : ByteArray
  bytePos : Nat
  bitPos : Nat
  hpos : bytePos ≤ data.size
  hend : bytePos = data.size → bitPos = 0
  hbit : bitPos < 8
deriving Repr

-- Small power of two for bit-window masks.
def lowPowNat (n : Nat) : Nat :=
  1 <<< n

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

def BitReader.readBitsAuxAcc (br : BitReader) (n shift acc : Nat) : Nat × BitReader :=
  match n with
  | 0 => (acc, br)
  | n + 1 =>
      let (bit, br') := br.readBit
      readBitsAuxAcc br' n (shift + 1) (acc ||| (bit <<< shift))

def BitReader.readBitsAux (br : BitReader) (n : Nat) : Nat × BitReader :=
  readBitsAuxAcc br n 0 0

-- Fast path for small bit windows using a 32-bit byte window.
def BitReader.readBitsFastU32 (br : BitReader) (n : Nat)
    (_h : br.bitIndex + n <= br.data.size * 8) : Nat × BitReader := by
  by_cases hzero : n = 0
  · subst hzero
    exact (0, br)
  by_cases hsmall : n <= 24
  · by_cases hnext : br.bytePos + 3 < br.data.size
    · let b0 := br.data.get br.bytePos (by omega)
      let b1 := br.data.get (br.bytePos + 1) (by omega)
      let b2 := br.data.get (br.bytePos + 2) (by omega)
      let b3 := br.data.get (br.bytePos + 3) (by omega)
      let w0 : UInt32 := UInt32.ofNat b0.toNat
      let w1 : UInt32 := UInt32.shiftLeft (UInt32.ofNat b1.toNat) (UInt32.ofNat 8)
      let w2 : UInt32 := UInt32.shiftLeft (UInt32.ofNat b2.toNat) (UInt32.ofNat 16)
      let w3 : UInt32 := UInt32.shiftLeft (UInt32.ofNat b3.toNat) (UInt32.ofNat 24)
      let word : UInt32 := w0 ||| w1 ||| w2 ||| w3
      let bitsU : UInt32 :=
        (UInt32.shiftRight word (UInt32.ofNat br.bitPos)) %
          (UInt32.shiftLeft (1 : UInt32) (UInt32.ofNat n))
      let bits : Nat := bitsU.toNat
      let next := br.bitPos + n
      let mk (nextBytePos nextBitPos : Nat) (hbit : nextBitPos < 8)
          (hlt : nextBytePos < br.data.size) : Nat × BitReader :=
        (bits,
          { data := br.data
            bytePos := nextBytePos
            bitPos := nextBitPos
            hpos := Nat.le_of_lt hlt
            hend := by
              intro hEq
              exact (False.elim ((Nat.ne_of_lt hlt) hEq))
            hbit := hbit })
      by_cases hlt1 : next < 8
      · have hlt : br.bytePos < br.data.size := by omega
        exact mk br.bytePos next hlt1 hlt
      · by_cases hlt2 : next < 16
        · have hbit' : next - 8 < 8 := by omega
          have hlt : br.bytePos + 1 < br.data.size := by omega
          exact mk (br.bytePos + 1) (next - 8) hbit' hlt
        · by_cases hlt3 : next < 24
          · have hbit' : next - 16 < 8 := by omega
            have hlt : br.bytePos + 2 < br.data.size := by omega
            exact mk (br.bytePos + 2) (next - 16) hbit' hlt
          · have hnextle : next <= 31 := by
              have hb : br.bitPos ≤ 7 := (Nat.lt_succ_iff.mp br.hbit)
              have hn : n <= 24 := hsmall
              have : br.bitPos + n <= 7 + 24 := by omega
              simpa [next] using this
            have hbit' : next - 24 <= 7 := by omega
            have hbit'' : next - 24 < 8 := by
              exact lt_of_le_of_lt hbit' (by decide)
            have hlt : br.bytePos + 3 < br.data.size := by omega
            exact mk (br.bytePos + 3) (next - 24) hbit'' hlt
    · exact br.readBitsAux n
  · exact br.readBitsAux n

def BitReader.readBits (br : BitReader) (n : Nat)
    (_h : br.bitIndex + n <= br.data.size * 8) : Nat × BitReader := by
  exact br.readBitsFastU32 n _h

-- Faster small-bit reader when the requested window stays inside the current byte.
set_option linter.unnecessarySimpa false
def BitReader.readBitsFast (br : BitReader) (n : Nat)
    (h : br.bitIndex + n <= br.data.size * 8) : Nat × BitReader := by
  by_cases hzero : n = 0
  · subst hzero
    exact (0, br)
  by_cases hsmall : n <= 8
  · by_cases hspan : br.bitPos + n < 8
    · have hlt : br.bytePos < br.data.size := by
        by_cases hEq : br.bytePos = br.data.size
        · have hbit0 : br.bitPos = 0 := br.hend hEq
          have hindex : br.bitIndex = br.data.size * 8 := by
            simp [BitReader.bitIndex, hEq, hbit0]
          have hn : 0 < n := Nat.pos_of_ne_zero hzero
          have hgt : br.bitIndex + n > br.data.size * 8 := by
            have : br.data.size * 8 < br.data.size * 8 + n := by
              exact Nat.lt_add_of_pos_right hn
            simpa [hindex, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
          exact (False.elim ((not_lt_of_ge h) hgt))
        · exact lt_of_le_of_ne br.hpos hEq
      let byte := br.data.get br.bytePos hlt
      let bits := (byte.toNat >>> br.bitPos) % lowPowNat n
      let nextBitPos := br.bitPos + n
      let hend' : br.bytePos = br.data.size → nextBitPos = 0 := by
        intro hEq
        have : False := by
          simpa [hEq] using hlt
        exact (False.elim this)
      exact
        (bits,
          { data := br.data
            bytePos := br.bytePos
            bitPos := nextBitPos
            hpos := br.hpos
            hend := hend'
            hbit := hspan })
    · exact br.readBits n h
  · exact br.readBits n h
set_option linter.unnecessarySimpa true

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
deriving Repr, DecidableEq

/-- Represents the valid DEFLATE edge case where a dynamic block has no distance codes at all. -/
def emptyHuffman : Huffman :=
  { maxLen := 0, table := #[#[]] }

def huffmanEmptyTable (maxLen : Nat) : Array (Array (Option Nat)) :=
  Array.ofFn (fun idx : Fin (maxLen + 1) =>
    if idx.val == 0 then #[] else Array.replicate (1 <<< idx.val) none)

def fillHuffmanTableAux (lengths : Array Nat) (i : Nat)
    (nextCode : Array Nat) (table : Array (Array (Option Nat))) :
    Option (Array (Array (Option Nat))) :=
  if h : i < lengths.size then
    let len := lengths[i]
    if len > 0 then
      let codeVal := nextCode[len]!
      if codeVal >= (1 <<< len) then
        none
      else
        let nextCode := nextCode.set! len (codeVal + 1)
        let rev := reverseBits codeVal len
        let row := table[len]!
        if rev >= row.size then
          none
        else
          let row' := row.set! rev (some i)
          let table := table.set! len row'
          fillHuffmanTableAux lengths (i + 1) nextCode table
    else
      fillHuffmanTableAux lengths (i + 1) nextCode table
  else
    some table
termination_by lengths.size - i
decreasing_by
  all_goals
    have hlt : i < lengths.size := h
    exact Nat.sub_lt_sub_left (k := i) (m := lengths.size) (n := i + 1)
      hlt (Nat.lt_succ_self i)

def mkHuffman (lengths : Array Nat) : Option Huffman :=
  let maxLen := maxCodeLenAux lengths 0 0
  if maxLen == 0 then
    none
  else
    let count := countCodeLengthsAux lengths 0 (Array.replicate (maxLen + 1) 0)
    let nextCode0 : Array Nat := Array.replicate (maxLen + 1) 0
    let (_, nextCode) := nextCodesAux count maxLen 1 0 nextCode0
    match fillHuffmanTableAux lengths 0 nextCode (huffmanEmptyTable maxLen) with
    | none => none
    | some table => some { maxLen, table }

/-- Detects the dynamic-table special case where every advertised code length is zero. -/
def allZeroCodeLengths (lengths : Array Nat) : Bool :=
  lengths.all (fun len => len == 0)

/-- Builds the dynamic distance table at the parser boundary, including literal-only blocks. -/
def buildDynamicDistTable (distLengths : Array Nat) : Option Huffman :=
  match mkHuffman distLengths with
  | some table => some table
  | none =>
      if allZeroCodeLengths distLengths then
        some emptyHuffman
      else
        none

def Huffman.decodeFuel (h : Huffman) (fuel code len : Nat) (br : BitReader) :
    Option (Nat × BitReader) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if br.bytePos < br.data.size then
        let (bit, br') := br.readBit
        let code' := code ||| (bit <<< len)
        let len' := len + 1
        if hlen : h.table.size <= len' then
          Huffman.decodeFuel h fuel code' len' br'
        else
          let row := Array.getInternal h.table len' (Nat.lt_of_not_ge hlen)
          if hcode : code' < row.size then
            match Array.getInternal row code' hcode with
            | some sym => some (sym, br')
            | none => Huffman.decodeFuel h fuel code' len' br'
          else
            Huffman.decodeFuel h fuel code' len' br'
      else
        none

def Huffman.decode (h : Huffman) (br : BitReader) : Option (Nat × BitReader) :=
  Huffman.decodeFuel h h.maxLen 0 0 br

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

def copyDistanceFast (out : ByteArray) (distance len : Nat) : Option ByteArray :=
  if _hbad : distance = 0 ∨ distance > out.size then
    none
  else if distance = 1 then
    some <| Id.run do
      let last := out.get! (out.size - 1)
      let mut out := out
      for _ in [0:len] do
        out := out.push last
      return out
  else
    some <| Id.run do
      let total := out.size + len
      let mut dest := ByteArray.mk <| Array.replicate total 0
      dest := out.copySlice 0 dest 0 out.size
      let mut pos := out.size
      let mut remaining := len
      while remaining > 0 do
        let chunk := Nat.min distance remaining
        let src := pos - distance
        dest := dest.copySlice src dest pos chunk
        pos := pos + chunk
        remaining := remaining - chunk
      return dest

def copyDistance (out : ByteArray) (distance len : Nat) : Option ByteArray :=
  copyDistanceFast out distance len

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

def decodeCompressedBlockFuel (fuel : Nat) (litLen dist : Huffman) (br : BitReader)
    (out : ByteArray) : Option (BitReader × ByteArray) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      let hLengthExtraSize : lengthExtra.size = 29 := by decide
      let hDistBasesSize : distBases.size = 30 := by decide
      let hDistExtraSize : distExtra.size = 30 := by decide
      let (sym, br') ← litLen.decode br
      if sym < 256 then
        decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
      else if sym == 256 then
        return (br', out)
      else if hlen : 257 ≤ sym ∧ sym ≤ 285 then
        let idx := sym - 257
        have hidxle : idx ≤ 28 := by
          dsimp [idx]
          omega
        have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
        have hidxExtra : idx < lengthExtra.size := by simpa [hLengthExtraSize] using hidxlt
        let extra := Array.getInternal lengthExtra idx hidxExtra
        if hbits : br'.bitIndex + extra <= br'.data.size * 8 then
          let (len, br'') := decodeLength sym br' hlen (by simpa using hbits)
          let (distSym, br''') ← dist.decode br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD <= br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeCompressedBlockFuel fuel litLen dist br'''' out'
            else
              none
          else
            none
        else
          none
      else
        none

def decodeCompressedBlock (litLen dist : Huffman) (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) :=
  decodeCompressedBlockFuel (br.data.size * 8 + 1) litLen dist br out

def readDynamicTablesLengthsFuel (fuel total : Nat) (codeLenTable : Huffman) (br : BitReader)
    (lengths : Array Nat) : Option (Array Nat × BitReader) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      if lengths.size >= total then
        return (lengths, br)
      let (sym, br') ← codeLenTable.decode br
      let mut lengthsCur := lengths
      let mut brCur := br'
      if sym <= 15 then
        lengthsCur := lengthsCur.push sym
      else if sym == 16 then
        if lengthsCur.size == 0 then
          none
        let (extra, br'') ←
          if h : brCur.bitIndex + 2 <= brCur.data.size * 8 then
            some (brCur.readBits 2 h)
          else
            none
        brCur := br''
        let repeatCount := 3 + extra
        let prev := lengthsCur[lengthsCur.size - 1]!
        for _ in [0:repeatCount] do
          lengthsCur := lengthsCur.push prev
      else if sym == 17 then
        let (extra, br'') ←
          if h : brCur.bitIndex + 3 <= brCur.data.size * 8 then
            some (brCur.readBits 3 h)
          else
            none
        brCur := br''
        let repeatCount := 3 + extra
        for _ in [0:repeatCount] do
          lengthsCur := lengthsCur.push 0
      else if sym == 18 then
        let (extra, br'') ←
          if h : brCur.bitIndex + 7 <= brCur.data.size * 8 then
            some (brCur.readBits 7 h)
          else
            none
        brCur := br''
        let repeatCount := 11 + extra
        for _ in [0:repeatCount] do
          lengthsCur := lengthsCur.push 0
      else
        none
      readDynamicTablesLengthsFuel fuel total codeLenTable brCur lengthsCur

def readDynamicTables (br : BitReader) : Option (Huffman × Huffman × BitReader) := do
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
  let mut brCur := br
  for i in [0:hclen] do
    let (len, br') ←
      if h : brCur.bitIndex + 3 <= brCur.data.size * 8 then
        some (brCur.readBits 3 h)
      else
        none
    codeLenLengths := codeLenLengths.set! order[i]! len
    brCur := br'
  let codeLenTable ← mkHuffman codeLenLengths
  let total := hlit + hdist
  let lengths0 : Array Nat := Array.mkEmpty total
  let (lengths, brNext) ←
    readDynamicTablesLengthsFuel (brCur.data.size * 8 + 1) total codeLenTable brCur lengths0
  brCur := brNext
  if lengths.size != total then
    none
  let litLenLengths := lengths.extract 0 hlit
  let distLengths := lengths.extract hlit (hlit + hdist)
  let litLenTable ← mkHuffman litLenLengths
  let distTable ← buildDynamicDistTable distLengths
  return (litLenTable, distTable, brCur)

def fixedLitLenRow7 : Array (Option Nat) :=
  Array.ofFn (fun i : Fin (1 <<< 7) =>
    let code := reverseBits i.val 7
    if code < 24 then
      some (256 + code)
    else
      none)

def fixedLitLenRow8 : Array (Option Nat) :=
  Array.ofFn (fun i : Fin (1 <<< 8) =>
    let code := reverseBits i.val 8
    if code < 192 then
      if 48 <= code then
        some (code - 48)
      else
        none
    else if code < 200 then
      some (code - 192 + 280)
    else
      none)

def fixedLitLenRow9 : Array (Option Nat) :=
  Array.ofFn (fun i : Fin (1 <<< 9) =>
    let code := reverseBits i.val 9
    if 400 <= code then
      some (code - 400 + 144)
    else
      none)

def fixedLitLenHuffman : Huffman :=
  { maxLen := 9
    table := #[
      #[],
      Array.replicate (1 <<< 1) none,
      Array.replicate (1 <<< 2) none,
      Array.replicate (1 <<< 3) none,
      Array.replicate (1 <<< 4) none,
      Array.replicate (1 <<< 5) none,
      Array.replicate (1 <<< 6) none,
      fixedLitLenRow7,
      fixedLitLenRow8,
      fixedLitLenRow9
    ] }

-- Decode a single fixed-Huffman literal/length symbol (literal-only fast path).
def decodeFixedLiteralSym (br : BitReader) : Option (Nat × BitReader) := do
  let (bits7, br7) ←
    if h : br.bitIndex + 7 <= br.data.size * 8 then
      some (br.readBitsFast 7 h)
    else
      none
  match fixedLitLenRow7[bits7]? with
  | some (some sym) =>
      return (sym, br7)
  | _ =>
      let (bit8, br8) ←
        if h : br7.bitIndex + 1 <= br7.data.size * 8 then
          some (br7.readBitsFast 1 h)
        else
          none
      let bits8 := bits7 ||| (bit8 <<< 7)
      match fixedLitLenRow8[bits8]? with
      | some (some sym) =>
          return (sym, br8)
      | _ =>
          let (bit9, br9) ←
            if h : br8.bitIndex + 1 <= br8.data.size * 8 then
              some (br8.readBitsFast 1 h)
            else
              none
          let bits9 := bits8 ||| (bit9 <<< 8)
          match fixedLitLenRow9[bits9]? with
          | some (some sym) =>
              return (sym, br9)
          | _ =>
              none

-- Decode a single fixed-Huffman literal/length symbol using a 9-bit table peek.
def decodeFixedLiteralSymFast9 (br : BitReader) : Option (Nat × BitReader) := do
  if h9 : br.bitIndex + 9 <= br.data.size * 8 then
    let (bits9, br9) := br.readBitsFastU32 9 h9
    let bits7 := bits9 % 2 ^ 7
    match fixedLitLenRow7[bits7]? with
    | some (some sym) =>
        if h7 : br.bitIndex + 7 <= br.data.size * 8 then
          let br7 := (br.readBitsFastU32 7 h7).2
          return (sym, br7)
        else
          none
    | _ =>
        let bits8 := bits9 % 2 ^ 8
        match fixedLitLenRow8[bits8]? with
        | some (some sym) =>
            if h8 : br.bitIndex + 8 <= br.data.size * 8 then
              let br8 := (br.readBitsFastU32 8 h8).2
              return (sym, br8)
            else
              none
        | _ =>
            match fixedLitLenRow9[bits9]? with
            | some (some sym) =>
                return (sym, br9)
            | _ =>
                none
  else
    decodeFixedLiteralSym br

-- Decode a fixed-Huffman block that is restricted to literals and end-of-block.
def decodeFixedLiteralBlockFuel (fuel : Nat) (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) := do
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let (sym, br') ← decodeFixedLiteralSym br
      if sym < 256 then
        decodeFixedLiteralBlockFuel fuel br' (out.push (u8 sym))
      else if sym == 256 then
        return (br', out)
      else
        none

def decodeFixedLiteralBlock (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) :=
  decodeFixedLiteralBlockFuel (br.data.size * 8) br out

def decodeFixedDistanceSym (br : BitReader) : Option (Nat × BitReader) := do
  if h : br.bitIndex + 5 <= br.data.size * 8 then
    let (bits, br') := br.readBitsFast 5 h
    some (reverseBits bits 5, br')
  else
    none

def decodeFixedBlockFuel (fuel : Nat) (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) := do
  match fuel with
  | 0 => none
  | fuel + 1 => do
      let hLengthExtraSize : lengthExtra.size = 29 := by decide
      let hDistBasesSize : distBases.size = 30 := by decide
      let hDistExtraSize : distExtra.size = 30 := by decide
      let (sym, br') ← decodeFixedLiteralSym br
      if sym < 256 then
        decodeFixedBlockFuel fuel br' (out.push (u8 sym))
      else if sym == 256 then
        return (br', out)
      else if hlen : 257 ≤ sym ∧ sym ≤ 285 then
        let idx := sym - 257
        have hidxle : idx ≤ 28 := by
          dsimp [idx]
          omega
        have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
        have hidxExtra : idx < lengthExtra.size := by simpa [hLengthExtraSize] using hidxlt
        let extra := Array.getInternal lengthExtra idx hidxExtra
        if hbits : br'.bitIndex + extra <= br'.data.size * 8 then
          let (len, br'') := decodeLength sym br' hlen (by simpa using hbits)
          let (distSym, br''') ← decodeFixedDistanceSym br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD <= br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeFixedBlockFuel fuel br'''' out'
            else
              none
          else
            none
        else
          none
      else
        none

def decodeFixedBlockFuelFast (fuel : Nat) (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) := do
  match fuel with
  | 0 => none
  | fuel + 1 => do
      let hLengthExtraSize : lengthExtra.size = 29 := by decide
      let hDistBasesSize : distBases.size = 30 := by decide
      let hDistExtraSize : distExtra.size = 30 := by decide
      let (sym, br') ← decodeFixedLiteralSymFast9 br
      if sym < 256 then
        decodeFixedBlockFuelFast fuel br' (out.push (u8 sym))
      else if sym == 256 then
        return (br', out)
      else if hlen : 257 ≤ sym ∧ sym ≤ 285 then
        let idx := sym - 257
        have hidxle : idx ≤ 28 := by
          dsimp [idx]
          omega
        have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
        have hidxExtra : idx < lengthExtra.size := by simpa [hLengthExtraSize] using hidxlt
        let extra := Array.getInternal lengthExtra idx hidxExtra
        if hbits : br'.bitIndex + extra <= br'.data.size * 8 then
          let (len, br'') := decodeLength sym br' hlen (by simpa using hbits)
          let (distSym, br''') ← decodeFixedDistanceSym br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD <= br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeFixedBlockFuelFast fuel br'''' out'
            else
              none
          else
            none
        else
          none
      else
        none

def decodeFixedBlockFast (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) :=
  decodeFixedBlockFuelFast (br.data.size * 8 + 1) br out

def decodeFixedBlockSpec (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) :=
  match decodeFixedLiteralBlock br out with
  | some res => some res
  | none => decodeFixedBlockFuel (br.data.size * 8 + 1) br out

def decodeFixedBlock (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) :=
  decodeFixedBlockFast br out

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

-- Decode deflate blocks with a fuel bound to guarantee termination.
def zlibDecompressLoopFuel (fuel : Nat) (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) := do
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let (hdr, br2) ←
        if h : br.bitIndex + 3 <= br.data.size * 8 then
          some (br.readBits 3 h)
        else
          none
      let bfinal := hdr % 2
      let btype := (hdr >>> 1) % 4
      let mut br := br2
      let mut out := out
      if btype == 0 then
        br := br.alignByte
        if h : br.bytePos + 3 < br.data.size then
          let len := readU16LE br.data br.bytePos (by omega)
          let nlen := readU16LE br.data (br.bytePos + 2) (by omega)
          if len + nlen != uint16MaxValue then
            none
          let start := br.bytePos + 4
          if hlen : start + len > br.data.size then
            none
          else
            out := out ++ br.data.extract start (start + len)
            have hle : start + len ≤ br.data.size := Nat.le_of_not_gt hlen
            br := {
              data := br.data
              bytePos := start + len
              bitPos := 0
              hpos := hle
              hend := by intro _; rfl
              hbit := by decide
            }
        else
          none
      else if btype == 1 then
        let (br', out') ← decodeFixedBlock br out
        br := br'
        out := out'
      else if btype == 2 then
        let (litLenTable, distTable, br') ← readDynamicTables br
        let (br'', out') ← decodeCompressedBlock litLenTable distTable br' out
        br := br''
        out := out'
      else
        none
      if bfinal == 1 then
        return (br, out)
      else
        zlibDecompressLoopFuel fuel br out

-- Decode deflate blocks until the final block, returning the reader and output.
def zlibDecompressLoop (br : BitReader) (out : ByteArray) : Option (BitReader × ByteArray) :=
  zlibDecompressLoopFuel (br.data.size * 8 + 1) br out

def zlibDecompress (data : ByteArray) (hsize : 2 <= data.size) : Option ByteArray := do
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
  let deflated := data.extract 2 (data.size - 4)
  let br0 : BitReader := {
    data := deflated
    bytePos := 0
    bitPos := 0
    hpos := by exact Nat.zero_le _
    hend := by intro _; rfl
    hbit := by decide
  }
  let out := ByteArray.empty
  let (br, out) ← zlibDecompressLoop br0 out
  let brAligned := br.alignByte
  let adlerPos := brAligned.bytePos + 2
  if hAdler : adlerPos + 3 < data.size then
    let adlerExpected := readU32BE data adlerPos hAdler
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
    if len + nlen != uint16MaxValue then
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
def inflateStored (data : ByteArray) : Option ByteArray := do
  if h : 0 < data.size then
    let (payload, rest) ← inflateStoredAux data h
    if rest.size == 0 then
      return payload
    else
      none
  else
    none

-- Tail-recursive stored-block inflater used for the runtime implementation.
-- Fast path for zlib streams that use only stored (uncompressed) deflate blocks.
def zlibDecompressStored (data : ByteArray) (hsize : 2 <= data.size) : Option ByteArray := do
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
  interlace : Nat := 0
deriving Repr

inductive PngTransparency where
  | gray1 (gray : Bool)
  | gray8 (gray : UInt8)
  | rgb8 (r g b : UInt8)
  | gray16 (gray : UInt16)
  | rgb16 (r g b : UInt16)
deriving Repr, DecidableEq

inductive PngBackground where
  | gray1 (gray : Bool)
  | gray8 (gray : UInt8)
  | rgb8 (r g b : UInt8)
  | gray16 (gray : UInt16)
  | rgb16 (r g b : UInt16)
deriving Repr, DecidableEq

structure PngMetadata where
  transparency : Option PngTransparency := none
  background : Option PngBackground := none
  gamma : Option Nat := none
  chromaticities : Option PngChromaticities := none
  srgb : Option PngSrgbIntent := none
  physical : Option PngPhysicalPixelDimensions := none
  modificationTime : Option PngTime := none
deriving Repr, DecidableEq

def PngMetadata.empty : PngMetadata :=
  { transparency := none
    background := none
    gamma := none
    chromaticities := none
    srgb := none
    physical := none
    modificationTime := none }

structure PngDecodeResult (px : Type u) [Pixel px] where
  bitmap : Bitmap px
  metadata : PngMetadata

structure PngDecodeGray1Result where
  bitmap : BitmapGray1
  metadata : PngMetadata

structure PngParsed where
  header : PngHeader
  idat : ByteArray
  metadata : PngMetadata
deriving Repr

def readU16BE! (bytes : ByteArray) (pos : Nat) : Nat :=
  ((bytes.get! pos).toNat <<< 8) + (bytes.get! (pos + 1)).toNat

def readU16BEUInt16! (bytes : ByteArray) (pos : Nat) : UInt16 :=
  UInt16.ofNat (readU16BE! bytes pos)

def readI32BE (bytes : ByteArray) (pos : Nat) (h : pos + 3 < bytes.size) : Int :=
  (UInt32.ofNat (readU32BE bytes pos h)).toInt32.toInt

def parseGammaData (data : ByteArray) : Option Nat := do
  if hlen : data.size = 4 then
    let gammaScaled := readU32BE data 0 (by omega)
    if gammaScaled == 0 then
      none
    else
      some gammaScaled
  else
    none

def parseChrmData (data : ByteArray) : Option PngChromaticities := do
  if hlen : data.size = 32 then
    some
      { white := { x := readI32BE data 0 (by omega), y := readI32BE data 4 (by omega) }
        red := { x := readI32BE data 8 (by omega), y := readI32BE data 12 (by omega) }
        green := { x := readI32BE data 16 (by omega), y := readI32BE data 20 (by omega) }
        blue := { x := readI32BE data 24 (by omega), y := readI32BE data 28 (by omega) } }
  else
    none

def parseSrgbData (data : ByteArray) : Option PngSrgbIntent := do
  if data.size != 1 then
    none
  else
    PngSrgbIntent.ofByte (data.get! 0)

def parseTimeData (data : ByteArray) : Option PngTime := do
  if data.size != 7 then
    none
  else
    let time : PngTime :=
      { year := readU16BE! data 0
        month := (data.get! 2).toNat
        day := (data.get! 3).toNat
        hour := (data.get! 4).toNat
        minute := (data.get! 5).toNat
        second := (data.get! 6).toNat }
    if time.valid then
      some time
    else
      none

def parsePhysData (data : ByteArray) : Option PngPhysicalPixelDimensions := do
  if hlen : data.size = 9 then
    let unit ← PngPhysicalUnit.ofByte (data.get! 8)
    some
      { xPixelsPerUnit := readU32BE data 0 (by omega)
        yPixelsPerUnit := readU32BE data 4 (by omega)
        unit }
  else
    none

def parseTrnsData (hdr : PngHeader) (data : ByteArray) : Option PngTransparency := do
  if hdr.colorType == 0 then
    if data.size != 2 then
      none
    else if hdr.bitDepth == 1 then
      let gray := readU16BE! data 0
      if gray ≤ 1 then
        some (.gray1 (gray != 0))
      else
        none
    else if hdr.bitDepth == 8 then
      let gray := readU16BE! data 0
      if gray ≤ 255 then
        some (.gray8 (u8 gray))
      else
        none
    else if hdr.bitDepth == 16 then
      some (.gray16 (readU16BEUInt16! data 0))
    else
      none
  else if hdr.colorType == 2 then
    if data.size != 6 then
      none
    else if hdr.bitDepth == 8 then
      let r := readU16BE! data 0
      let g := readU16BE! data 2
      let b := readU16BE! data 4
      if r ≤ 255 && g ≤ 255 && b ≤ 255 then
        some (.rgb8 (u8 r) (u8 g) (u8 b))
      else
        none
    else if hdr.bitDepth == 16 then
      some (.rgb16 (readU16BEUInt16! data 0) (readU16BEUInt16! data 2)
        (readU16BEUInt16! data 4))
    else
      none
  else
    none

def parseBkgdData (hdr : PngHeader) (data : ByteArray) : Option PngBackground := do
  if hdr.colorType == 0 || hdr.colorType == 4 then
    if data.size != 2 then
      none
    else if hdr.bitDepth == 1 then
      let gray := readU16BE! data 0
      if gray ≤ 1 then
        some (.gray1 (gray != 0))
      else
        none
    else if hdr.bitDepth == 8 then
      let gray := readU16BE! data 0
      if gray ≤ 255 then
        some (.gray8 (u8 gray))
      else
        none
    else if hdr.bitDepth == 16 then
      some (.gray16 (readU16BEUInt16! data 0))
    else
      none
  else if hdr.colorType == 2 || hdr.colorType == 6 then
    if data.size != 6 then
      none
    else if hdr.bitDepth == 8 then
      let r := readU16BE! data 0
      let g := readU16BE! data 2
      let b := readU16BE! data 4
      if r ≤ 255 && g ≤ 255 && b ≤ 255 then
        some (.rgb8 (u8 r) (u8 g) (u8 b))
      else
        none
    else if hdr.bitDepth == 16 then
      some (.rgb16 (readU16BEUInt16! data 0) (readU16BEUInt16! data 2)
        (readU16BEUInt16! data 4))
    else
      none
  else
    none

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
    let crcExpected := readU32BE bytes dataEnd (by omega)
    let crcActual := (crc32Chunk typBytes data).toNat
    if crcExpected == crcActual then
      some (typBytes, data, crcEnd)
    else
      none
  else
    none

def parseIHDRData (data : ByteArray) : Option PngHeader := do
  if hlen : data.size = 13 then
    let w := readU32BE data 0 (by omega)
    let h := readU32BE data 4 (by omega)
    let tail := data.extract 8 13
    let bitDepth := (tail.get! 0).toNat
    let colorType := (tail.get! 1).toNat
    let comp := (tail.get! 2).toNat
    let filter := (tail.get! 3).toNat
    let interlace := (tail.get! 4).toNat
    if comp != 0 || filter != 0 || (interlace != 0 && interlace != 1) then
      none
    return { width := w, height := h, colorType, bitDepth, interlace }
  else
    none

def isCriticalChunkType (typBytes : ByteArray) : Bool :=
  ((typBytes.get! 0).toNat &&& 0x20) == 0

def plteAllowedForColorType (colorType : Nat) : Bool :=
  colorType != 0 && colorType != 4

def pngBytesPerPixelForColorType? (colorType : Nat) : Option Nat :=
  if colorType == 0 then
    some 1
  else if colorType == 2 then
    some 3
  else if colorType == 4 then
    some 2
  else if colorType == 6 then
    some 4
  else
    none

def pngChannelCountForColorType? (colorType : Nat) : Option Nat :=
  if colorType == 0 then
    some 1
  else if colorType == 2 then
    some 3
  else if colorType == 4 then
    some 2
  else if colorType == 6 then
    some 4
  else
    none

def pngSampleBytesForBitDepth? (bitDepth : Nat) : Option Nat :=
  if bitDepth == 8 then
    some 1
  else if bitDepth == 16 then
    some 2
  else
    none

def pngBytesPerPixelForColorTypeAndBitDepth? (colorType bitDepth : Nat) : Option Nat := do
  let channels ← pngChannelCountForColorType? colorType
  let sampleBytes ← pngSampleBytesForBitDepth? bitDepth
  some (channels * sampleBytes)

def pngBitsPerPixelForColorTypeAndBitDepth? (colorType bitDepth : Nat) : Option Nat := do
  let channels ← pngChannelCountForColorType? colorType
  if colorType == 0 && bitDepth == 1 then
    some 1
  else if bitDepth == 8 || bitDepth == 16 then
    some (channels * bitDepth)
  else
    none

def pngRowBytesForColorTypeAndBitDepth? (width colorType bitDepth : Nat) : Option Nat := do
  let bitsPerPixel ← pngBitsPerPixelForColorTypeAndBitDepth? colorType bitDepth
  some ((width * bitsPerPixel + 7) / 8)

def pngFilterBppForColorTypeAndBitDepth? (colorType bitDepth : Nat) : Option Nat := do
  if colorType == 0 && bitDepth == 1 then
    some 1
  else
    pngBytesPerPixelForColorTypeAndBitDepth? colorType bitDepth

def pngColorTypeBitDepthSupported (colorType bitDepth : Nat) : Bool :=
  if colorType == 0 then
    bitDepth == 1 || bitDepth == 8 || bitDepth == 16
  else if colorType == 2 || colorType == 4 || colorType == 6 then
    bitDepth == 8 || bitDepth == 16
  else
    false

def pngBitDepthSupported (bitDepth : Nat) : Bool :=
  bitDepth == 1 || bitDepth == 8 || bitDepth == 16

structure PngParseState where
  header : Option PngHeader
  idat : ByteArray
  seenPLTE : Bool
  seenIDAT : Bool
  closedIDAT : Bool
  metadata : PngMetadata := PngMetadata.empty
deriving Repr

def parsePngSimple (bytes : ByteArray) (_hsize : 8 <= bytes.size) :
    Option (PngHeader × ByteArray) := do
  if bytes.extract 0 8 != pngSignature then
    none
  let pos := 8
  if hLen1 : pos + 3 < bytes.size then
    match readChunk bytes pos hLen1 with
    | some (typ1, data1, pos2) =>
        if typ1 != ihdrTypeBytes then
          none
        let hdr ← parseIHDRData data1
        if !pngColorTypeBitDepthSupported hdr.colorType hdr.bitDepth then
          none
        if hdr.colorType != 0 && hdr.colorType != 2 && hdr.colorType != 4 &&
            hdr.colorType != 6 then
          none
        if hLen2 : pos2 + 3 < bytes.size then
          match readChunk bytes pos2 hLen2 with
          | some (typ2, data2, pos3) =>
              if typ2 != idatTypeBytes then
                none
              if hLen3 : pos3 + 3 < bytes.size then
                match readChunk bytes pos3 hLen3 with
                | some (typ3, data3, pos4) =>
                    if typ3 != iendTypeBytes then
                      none
                    if data3.size != 0 then
                      none
                    if pos4 != bytes.size then
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


def parsePngLoopFuel (fuel : Nat) (bytes : ByteArray) (pos : Nat)
    (state : PngParseState) : Option (PngHeader × ByteArray) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      if _hpos : pos + 8 <= bytes.size then
        if hLen : pos + 3 < bytes.size then
          let len := readU32BE bytes pos hLen
          match readChunk bytes pos hLen with
          | some (typBytes, chunkData, posNext) =>
              match state.header with
              | none =>
                  if typBytes == ihdrTypeBytes then
                    if len != 13 then
                      none
                    let hdr ← parseIHDRData chunkData
                    parsePngLoopFuel fuel bytes posNext { state with header := some hdr }
                  else
                    none
              | some hdr =>
                  if typBytes == ihdrTypeBytes then
                    none
                  else if typBytes == plteTypeBytes then
                    if state.seenPLTE || state.seenIDAT then
                      none
                    if !plteAllowedForColorType hdr.colorType then
                      none
                    if chunkData.size % 3 != 0 then
                      none
                    parsePngLoopFuel fuel bytes posNext { state with seenPLTE := true }
                  else if typBytes == idatTypeBytes then
                    if state.closedIDAT then
                      none
                    if hdr.colorType == 3 && !state.seenPLTE then
                      none
                    parsePngLoopFuel fuel bytes posNext
                      { state with
                          idat := state.idat ++ chunkData
                          seenIDAT := true }
                  else if typBytes == iendTypeBytes then
                    if chunkData.size != 0 then
                      none
                    if !state.seenIDAT then
                      none
                    if posNext != bytes.size then
                      none
                    some (hdr, state.idat)
                  else if typBytes == trnsTypeBytes then
                    -- tRNS attaches transparency to color types 0/2/3; the decoder does not
                    -- honor it, and silently ignoring it would change pixel semantics.
                    none
                  else if typBytes == gamaTypeBytes then
                    if state.seenPLTE || state.seenIDAT then
                      none
                    if state.metadata.gamma.isSome then
                      none
                    let gamma ← parseGammaData chunkData
                    if state.metadata.srgb.isSome && gamma != 45455 then
                      none
                    parsePngLoopFuel fuel bytes posNext
                      { state with
                          metadata := { state.metadata with gamma := some gamma } }
                  else if typBytes == chrmTypeBytes then
                    if state.seenPLTE || state.seenIDAT then
                      none
                    if state.metadata.chromaticities.isSome then
                      none
                    let chromaticities ← parseChrmData chunkData
                    match state.metadata.srgb with
                    | some _ =>
                        if chromaticities = PngChromaticities.srgb then
                          parsePngLoopFuel fuel bytes posNext
                            { state with
                                metadata := { state.metadata with
                                  chromaticities := some chromaticities } }
                        else
                          none
                    | none =>
                        parsePngLoopFuel fuel bytes posNext
                          { state with
                              metadata := { state.metadata with
                                chromaticities := some chromaticities } }
                  else if typBytes == srgbTypeBytes then
                    if state.seenPLTE || state.seenIDAT then
                      none
                    if state.metadata.srgb.isSome then
                      none
                    let intent ← parseSrgbData chunkData
                    let continueWithSrgb :=
                        parsePngLoopFuel fuel bytes posNext
                          { state with
                              metadata := { state.metadata with srgb := some intent } }
                    match state.metadata.gamma with
                    | some gamma =>
                        if gamma != 45455 then
                          none
                        else
                          match state.metadata.chromaticities with
                          | some chromaticities =>
                              if chromaticities = PngChromaticities.srgb then
                                continueWithSrgb
                              else
                                none
                          | none =>
                              continueWithSrgb
                    | none =>
                        match state.metadata.chromaticities with
                        | some chromaticities =>
                            if chromaticities = PngChromaticities.srgb then
                              continueWithSrgb
                            else
                              none
                        | none =>
                            continueWithSrgb
                  else if typBytes == timeTypeBytes then
                    if state.metadata.modificationTime.isSome then
                      none
                    let modificationTime ← parseTimeData chunkData
                    parsePngLoopFuel fuel bytes posNext
                      { state with
                          closedIDAT := if state.seenIDAT then true else state.closedIDAT
                          metadata := { state.metadata with modificationTime := some modificationTime } }
                  else if typBytes == physTypeBytes then
                    if state.seenIDAT then
                      none
                    if state.metadata.physical.isSome then
                      none
                    let physical ← parsePhysData chunkData
                    parsePngLoopFuel fuel bytes posNext
                      { state with
                          metadata := { state.metadata with physical := some physical } }
                  else if typBytes == sbitTypeBytes then
                    -- sBIT records the significant bit count per channel; ignoring it would
                    -- silently misrepresent pixel precision.
                    none
                  else if isCriticalChunkType typBytes then
                    none
                  else if state.seenIDAT then
                    parsePngLoopFuel fuel bytes posNext { state with closedIDAT := true }
                  else
                    parsePngLoopFuel fuel bytes posNext state
          | none =>
              none
        else
          none
      else
        none

def parsePng (bytes : ByteArray) (_hsize : 8 <= bytes.size) :
    Option (PngHeader × ByteArray) := do
  if let some res := parsePngSimple bytes _hsize then
    return res
  if bytes.extract 0 8 != pngSignature then
    none
  parsePngLoopFuel (bytes.size + 1) bytes 8
    { header := none
      idat := ByteArray.empty
      seenPLTE := false
      seenIDAT := false
      closedIDAT := false
      metadata := PngMetadata.empty }

structure PngMetadataParseState where
  header : Option PngHeader
  idat : ByteArray
  seenPLTE : Bool
  seenIDAT : Bool
  closedIDAT : Bool
  metadata : PngMetadata
deriving Repr

def parsePngSimpleWithMetadata (bytes : ByteArray) (hsize : 8 <= bytes.size) :
    Option PngParsed := do
  let (hdr, idat) ← parsePngSimple bytes hsize
  return {
    header := hdr
    idat := idat
    metadata := PngMetadata.empty
  }

def parsePngLoopFuelWithMetadata (fuel : Nat) (bytes : ByteArray) (pos : Nat)
    (state : PngMetadataParseState) : Option PngParsed :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      if _hpos : pos + 8 <= bytes.size then
        if hLen : pos + 3 < bytes.size then
          let len := readU32BE bytes pos hLen
          match readChunk bytes pos hLen with
          | some (typBytes, chunkData, posNext) =>
              match state.header with
              | none =>
                  if typBytes == ihdrTypeBytes then
                    if len != 13 then
                      none
                    let hdr ← parseIHDRData chunkData
                    parsePngLoopFuelWithMetadata fuel bytes posNext { state with header := some hdr }
                  else
                    none
              | some hdr =>
                  if typBytes == ihdrTypeBytes then
                    none
                  else if typBytes == plteTypeBytes then
                    if state.seenPLTE || state.seenIDAT then
                      none
                    if state.metadata.transparency.isSome || state.metadata.background.isSome then
                      none
                    if !plteAllowedForColorType hdr.colorType then
                      none
                    if chunkData.size % 3 != 0 then
                      none
                    parsePngLoopFuelWithMetadata fuel bytes posNext { state with seenPLTE := true }
                  else if typBytes == idatTypeBytes then
                    if state.closedIDAT then
                      none
                    if hdr.colorType == 3 && !state.seenPLTE then
                      none
                    parsePngLoopFuelWithMetadata fuel bytes posNext
                      { state with
                          idat := state.idat ++ chunkData
                          seenIDAT := true }
                  else if typBytes == iendTypeBytes then
                    if chunkData.size != 0 then
                      none
                    if !state.seenIDAT then
                      none
                    if posNext != bytes.size then
                      none
                    some { header := hdr, idat := state.idat, metadata := state.metadata }
                  else if typBytes == trnsTypeBytes then
                    if state.seenIDAT then
                      none
                    if state.metadata.transparency.isSome then
                      none
                    let trns ← parseTrnsData hdr chunkData
                    parsePngLoopFuelWithMetadata fuel bytes posNext
                      { state with
                          metadata := { state.metadata with transparency := some trns } }
                  else if typBytes == bkgdTypeBytes then
                    if state.seenIDAT then
                      none
                    if state.metadata.background.isSome then
                      none
                    let bkgd ← parseBkgdData hdr chunkData
                    parsePngLoopFuelWithMetadata fuel bytes posNext
                      { state with
                          metadata := { state.metadata with background := some bkgd } }
                  else if typBytes == gamaTypeBytes then
                    if state.seenPLTE || state.seenIDAT then
                      none
                    if state.metadata.gamma.isSome then
                      none
                    let gamma ← parseGammaData chunkData
                    if state.metadata.srgb.isSome && gamma != 45455 then
                      none
                    parsePngLoopFuelWithMetadata fuel bytes posNext
                      { state with
                          metadata := { state.metadata with gamma := some gamma } }
                  else if typBytes == chrmTypeBytes then
                    if state.seenPLTE || state.seenIDAT then
                      none
                    if state.metadata.chromaticities.isSome then
                      none
                    let chromaticities ← parseChrmData chunkData
                    match state.metadata.srgb with
                    | some _ =>
                        if chromaticities = PngChromaticities.srgb then
                          parsePngLoopFuelWithMetadata fuel bytes posNext
                            { state with
                                metadata := { state.metadata with
                                  chromaticities := some chromaticities } }
                        else
                          none
                    | none =>
                        parsePngLoopFuelWithMetadata fuel bytes posNext
                          { state with
                              metadata := { state.metadata with
                                chromaticities := some chromaticities } }
                  else if typBytes == srgbTypeBytes then
                    if state.seenPLTE || state.seenIDAT then
                      none
                    if state.metadata.srgb.isSome then
                      none
                    let intent ← parseSrgbData chunkData
                    let continueWithSrgb :=
                        parsePngLoopFuelWithMetadata fuel bytes posNext
                          { state with
                              metadata := { state.metadata with srgb := some intent } }
                    match state.metadata.gamma with
                    | some gamma =>
                        if gamma != 45455 then
                          none
                        else
                          match state.metadata.chromaticities with
                          | some chromaticities =>
                              if chromaticities = PngChromaticities.srgb then
                                continueWithSrgb
                              else
                                none
                          | none =>
                              continueWithSrgb
                    | none =>
                        match state.metadata.chromaticities with
                        | some chromaticities =>
                            if chromaticities = PngChromaticities.srgb then
                              continueWithSrgb
                            else
                              none
                        | none =>
                            continueWithSrgb
                  else if typBytes == timeTypeBytes then
                    if state.metadata.modificationTime.isSome then
                      none
                    let modificationTime ← parseTimeData chunkData
                    parsePngLoopFuelWithMetadata fuel bytes posNext
                      { state with
                          closedIDAT := if state.seenIDAT then true else state.closedIDAT
                          metadata := { state.metadata with modificationTime := some modificationTime } }
                  else if typBytes == physTypeBytes then
                    if state.seenIDAT then
                      none
                    if state.metadata.physical.isSome then
                      none
                    let physical ← parsePhysData chunkData
                    parsePngLoopFuelWithMetadata fuel bytes posNext
                      { state with
                          metadata := { state.metadata with physical := some physical } }
                  else if typBytes == sbitTypeBytes then
                    -- sBIT records the significant bit count per channel; ignoring it would
                    -- silently misrepresent pixel precision.
                    none
                  else if isCriticalChunkType typBytes then
                    none
                  else if state.seenIDAT then
                    parsePngLoopFuelWithMetadata fuel bytes posNext { state with closedIDAT := true }
                  else
                    parsePngLoopFuelWithMetadata fuel bytes posNext state
          | none =>
              none
        else
          none
      else
        none

def parsePngWithMetadata (bytes : ByteArray) (_hsize : 8 <= bytes.size) :
    Option PngParsed := do
  if let some res := parsePngSimpleWithMetadata bytes _hsize then
    return res
  if bytes.extract 0 8 != pngSignature then
    none
  parsePngLoopFuelWithMetadata (bytes.size + 1) bytes 8
    { header := none
      idat := ByteArray.empty
      seenPLTE := false
      seenIDAT := false
      closedIDAT := false
      metadata := PngMetadata.empty }

def parsePngForDecode (bytes : ByteArray) (hsize : 8 <= bytes.size) :
    Option PngParsed := do
  match parsePngSimpleWithMetadata bytes hsize with
  | some parsed => some parsed
  | none => parsePngWithMetadata bytes hsize

def PngMetadata.pixelOnlyColorSpace (metadata : PngMetadata) : PngMetadata :=
  { PngMetadata.empty with
    gamma := metadata.gamma
    chromaticities := metadata.chromaticities
    srgb := metadata.srgb }

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

def filterResidualByte (sample predictor : UInt8) : UInt8 :=
  u8 (sample.toNat + 256 - predictor.toNat)

def filterRowPredictor (filter : PngRowFilter) (row prev : ByteArray) (bpp i : Nat) :
    UInt8 :=
  let a := if i >= bpp then row.get! (i - bpp) else (0 : UInt8)
  let b := if i < prev.size then prev.get! i else (0 : UInt8)
  let c := if i >= bpp && i < prev.size then prev.get! (i - bpp) else (0 : UInt8)
  match filter with
  | .none => 0
  | .sub => a
  | .up => b
  | .average => u8 ((a.toNat + b.toNat) / 2)
  | .paeth => u8 (paethPredictor a.toNat b.toNat c.toNat)

def filterRow (filter : PngRowFilter) (row prev : ByteArray) (bpp : Nat) : ByteArray :=
  match filter with
  | .none => row
  | _ =>
      Id.run do
        let rowLen := row.size
        let mut out := ByteArray.emptyWithCapacity rowLen
        for i in [0:rowLen] do
          let sample := row.get! i
          let predictor := filterRowPredictor filter row prev bpp i
          out := out.push (filterResidualByte sample predictor)
        return out

def filterScoreByte (b : UInt8) : Nat :=
  let n := b.toNat
  if n < 128 then n else 256 - n

def filterRowScore (row : ByteArray) : Nat :=
  Id.run do
    let mut score := 0
    for i in [0:row.size] do
      score := score + filterScoreByte (row.get! i)
    return score

def chooseLowerFilterScore (best candidate : PngRowFilter × ByteArray) :
    PngRowFilter × ByteArray :=
  if filterRowScore candidate.2 < filterRowScore best.2 then
    candidate
  else
    best

def adaptiveFilterRow (row prev : ByteArray) (bpp : Nat) : PngRowFilter × ByteArray :=
  let best : PngRowFilter × ByteArray := (.none, row)
  let best := chooseLowerFilterScore best (.sub, filterRow .sub row prev bpp)
  let best := chooseLowerFilterScore best (.up, filterRow .up row prev bpp)
  let best := chooseLowerFilterScore best (.average, filterRow .average row prev bpp)
  chooseLowerFilterScore best (.paeth, filterRow .paeth row prev bpp)

def filterRowForStrategy (strategy : PngFilterStrategy) (row prev : ByteArray) (bpp : Nat) :
    UInt8 × ByteArray :=
  match strategy with
  | .none => (PngRowFilter.none.toByte, row)
  | .fixed filter => (filter.toByte, filterRow filter row prev bpp)
  | .adaptive =>
      let chosen := adaptiveFilterRow row prev bpp
      (chosen.1.toByte, chosen.2)

structure Adam7Pass where
  startX : Nat
  startY : Nat
  stepX : Nat
  stepY : Nat
deriving Repr, DecidableEq

def adam7Passes : List Adam7Pass :=
  [ { startX := 0, startY := 0, stepX := 8, stepY := 8 }
  , { startX := 4, startY := 0, stepX := 8, stepY := 8 }
  , { startX := 0, startY := 4, stepX := 4, stepY := 8 }
  , { startX := 2, startY := 0, stepX := 4, stepY := 4 }
  , { startX := 0, startY := 2, stepX := 2, stepY := 4 }
  , { startX := 1, startY := 0, stepX := 2, stepY := 2 }
  , { startX := 0, startY := 1, stepX := 1, stepY := 2 } ]

def adam7PassDim (full start step : Nat) : Nat :=
  if start < full then
    ((full - 1 - start) / step) + 1
  else
    0

def adam7ScatterRow (row : ByteArray) (flat : ByteArray) (w bpp : Nat)
    (pass : Adam7Pass) (passY passWidth : Nat) : ByteArray :=
  Id.run do
    let mut flat := flat
    let dstY := pass.startY + passY * pass.stepY
    for passX in [0:passWidth] do
      let dstX := pass.startX + passX * pass.stepX
      let srcBase := passX * bpp
      let dstBase := (dstY * w + dstX) * bpp
      for k in [0:bpp] do
        flat := flat.set! (dstBase + k) (row.get! (srcBase + k))
    return flat

def decodeAdam7PassRows (raw : ByteArray) (w bpp : Nat) (pass : Adam7Pass)
    (passWidth passHeight passY offset : Nat) (prevRow flat : ByteArray) :
    Option (Nat × ByteArray) := do
  if hlt : passY < passHeight then
    let _ := hlt
    let rowBytes := passWidth * bpp
    if _hrow : offset + 1 + rowBytes ≤ raw.size then
      let filter := raw.get! offset
      let dataStart := offset + 1
      let rowData := raw.extract dataStart (dataStart + rowBytes)
      if hfilter : filter.toNat ≤ 4 then
        let row :=
          if filter.toNat = 0 then
            rowData
          else
            unfilterRow filter rowData prevRow bpp hfilter
        let flat := adam7ScatterRow row flat w bpp pass passY passWidth
        decodeAdam7PassRows raw w bpp pass passWidth passHeight (passY + 1)
          (dataStart + rowBytes) row flat
      else
        none
    else
      none
  else
    some (offset, flat)
termination_by passHeight - passY
decreasing_by
  have hpassY : passY < passHeight := hlt
  have hsucc : passY < passY + 1 := Nat.lt_succ_self passY
  exact Nat.sub_lt_sub_left hpassY hsucc

def decodeAdam7Passes (raw : ByteArray) (w h bpp offset : Nat) (flat : ByteArray) :
    List Adam7Pass -> Option (Nat × ByteArray)
  | [] => some (offset, flat)
  | pass :: passes => do
      let passWidth := adam7PassDim w pass.startX pass.stepX
      let passHeight :=
        if passWidth == 0 then
          0
        else
          adam7PassDim h pass.startY pass.stepY
      let (offset, flat) ←
        decodeAdam7PassRows raw w bpp pass passWidth passHeight 0 offset ByteArray.empty flat
      decodeAdam7Passes raw w h bpp offset flat passes

def adam7FlatToRawLoop (flat : ByteArray) (rowBytes h y : Nat) (raw : ByteArray) :
    ByteArray :=
  if hlt : y < h then
    let outOff := y * (rowBytes + 1)
    let start := y * rowBytes
    let raw := flat.copySlice start raw (outOff + 1) rowBytes
    adam7FlatToRawLoop flat rowBytes h (y + 1) raw
  else
    raw
termination_by h - y
decreasing_by
  have hy : y < h := hlt
  have hy' : y < y + 1 := Nat.lt_succ_self y
  exact Nat.sub_lt_sub_left hy hy'

def adam7FlatToFilterZeroRaw (flat : ByteArray) (w h bpp : Nat) : ByteArray :=
  let rowBytes := w * bpp
  let rawSize := h * (rowBytes + 1)
  let raw := ByteArray.mk <| Array.replicate rawSize 0
  adam7FlatToRawLoop flat rowBytes h 0 raw

def decodeAdam7ToFlatRaw? (raw : ByteArray) (w h bpp : Nat) : Option ByteArray := do
  let flatSize := w * h * bpp
  let flat0 := ByteArray.mk <| Array.replicate flatSize 0
  let (offset, flat) ← decodeAdam7Passes raw w h bpp 0 flat0 adam7Passes
  if offset != raw.size then
    none
  else
    some (adam7FlatToFilterZeroRaw flat w h bpp)

@[inline] def gray1BitAt (bytes : ByteArray) (w x y : Nat) : Bool :=
  let byte := bytes.get! (gray1ByteIndex w x y)
  gray1BitIsSet byte x

@[inline] def gray1SetFlatBit (flat : ByteArray) (w x y : Nat) (bit : Bool) :
    ByteArray :=
  let idx := gray1ByteIndex w x y
  let byte := flat.get! idx
  flat.set! idx (gray1SetBitInByte byte x bit)

def adam7ScatterRowGray1 (row : ByteArray) (flat : ByteArray) (w : Nat)
    (pass : Adam7Pass) (passY passWidth : Nat) : ByteArray :=
  Id.run do
    let mut flat := flat
    let dstY := pass.startY + passY * pass.stepY
    for passX in [0:passWidth] do
      let dstX := pass.startX + passX * pass.stepX
      flat := gray1SetFlatBit flat w dstX dstY (gray1BitAt row passWidth passX 0)
    return flat

def decodeAdam7Gray1PassRows (raw : ByteArray) (w : Nat) (pass : Adam7Pass)
    (passWidth passHeight passY offset : Nat) (prevRow flat : ByteArray) :
    Option (Nat × ByteArray) := do
  if hlt : passY < passHeight then
    let _ := hlt
    let rowBytes := gray1RowBytes passWidth
    if _hrow : offset + 1 + rowBytes ≤ raw.size then
      let filter := raw.get! offset
      let dataStart := offset + 1
      let rowData := raw.extract dataStart (dataStart + rowBytes)
      if hfilter : filter.toNat ≤ 4 then
        let row :=
          if filter.toNat = 0 then
            rowData
          else
            unfilterRow filter rowData prevRow 1 hfilter
        let flat := adam7ScatterRowGray1 row flat w pass passY passWidth
        decodeAdam7Gray1PassRows raw w pass passWidth passHeight (passY + 1)
          (dataStart + rowBytes) row flat
      else
        none
    else
      none
  else
    some (offset, flat)
termination_by passHeight - passY
decreasing_by
  have hpassY : passY < passHeight := hlt
  have hsucc : passY < passY + 1 := Nat.lt_succ_self passY
  exact Nat.sub_lt_sub_left hpassY hsucc

def decodeAdam7Gray1Passes (raw : ByteArray) (w h offset : Nat) (flat : ByteArray) :
    List Adam7Pass -> Option (Nat × ByteArray)
  | [] => some (offset, flat)
  | pass :: passes => do
      let passWidth := adam7PassDim w pass.startX pass.stepX
      let passHeight :=
        if passWidth == 0 then
          0
        else
          adam7PassDim h pass.startY pass.stepY
      let (offset, flat) ←
        decodeAdam7Gray1PassRows raw w pass passWidth passHeight 0 offset ByteArray.empty flat
      decodeAdam7Gray1Passes raw w h offset flat passes

def gray1FlatToFilterZeroRaw (flat : ByteArray) (w h : Nat) : ByteArray :=
  let rowBytes := gray1RowBytes w
  let rawSize := h * (rowBytes + 1)
  let raw := ByteArray.mk <| Array.replicate rawSize 0
  adam7FlatToRawLoop flat rowBytes h 0 raw

def decodeAdam7Gray1ToFlatRaw? (raw : ByteArray) (w h : Nat) : Option ByteArray := do
  let flatSize := gray1DataSize w h
  let flat0 := ByteArray.mk <| Array.replicate flatSize 0
  let (offset, flat) ← decodeAdam7Gray1Passes raw w h 0 flat0 adam7Passes
  if offset != raw.size then
    none
  else
    some (gray1FlatToFilterZeroRaw flat w h)

def normalizeRawByInterlace? (raw : ByteArray) (hdr : PngHeader) (bpp : Nat) :
    Option ByteArray :=
  if hdr.interlace == 0 then
    some raw
  else if hdr.interlace == 1 then
    decodeAdam7ToFlatRaw? raw hdr.width hdr.height bpp
  else
    none

def normalizeGray1RawByInterlace? (raw : ByteArray) (hdr : PngHeader) :
    Option ByteArray :=
  if hdr.interlace == 0 then
    some raw
  else if hdr.interlace == 1 then
    decodeAdam7Gray1ToFlatRaw? raw hdr.width hdr.height
  else
    none

def gray1FlatToSampleRaw (flat : ByteArray) (w h targetBitDepth : Nat) : ByteArray :=
  Id.run do
    let rowBytes := if targetBitDepth == 16 then w * 2 else w
    let mut raw := ByteArray.emptyWithCapacity (h * (rowBytes + 1))
    for y in [0:h] do
      raw := raw.push 0
      for x in [0:w] do
        let on := gray1BitAt flat w x y
        if targetBitDepth == 16 then
          if on then
            raw := raw.push 0xff
            raw := raw.push 0xff
          else
            raw := raw.push 0
            raw := raw.push 0
        else
          raw := raw.push (if on then 0xff else 0)
    return raw

def decodeRowDropAlpha (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let r := row.get! base
      let g := if bpp == 1 || bpp == 2 then r else row.get! (base + 1)
      let b := if bpp == 1 || bpp == 2 then r else row.get! (base + 2)
      let pixBase := (y * w + x) * bytesPerPixelRGB
      pixels := pixels.set! pixBase r
      pixels := pixels.set! (pixBase + 1) g
      pixels := pixels.set! (pixBase + 2) b
    return pixels

def backgroundToRGB (background : PngBackground) : UInt8 × UInt8 × UInt8 :=
  match background with
  | .gray1 gray =>
      let gray8 := if gray then 0xff else 0
      (gray8, gray8, gray8)
  | .gray8 gray => (gray, gray, gray)
  | .rgb8 r g b => (r, g, b)
  | .gray16 gray =>
      let gray8 := u8 (gray.toNat / 256)
      (gray8, gray8, gray8)
  | .rgb16 r g b => (u8 (r.toNat / 256), u8 (g.toNat / 256), u8 (b.toNat / 256))

def backgroundToGray (background : PngBackground) : UInt8 :=
  match background with
  | .gray1 gray => if gray then 0xff else 0
  | .gray8 gray => gray
  | .rgb8 r g b => u8 ((r.toNat + g.toNat + b.toNat) / 3)
  | .gray16 gray => u8 (gray.toNat / 256)
  | .rgb16 r g b => u8 (((r.toNat / 256) + (g.toNat / 256) + (b.toNat / 256)) / 3)

def u8ToUInt16Full (x : UInt8) : UInt16 :=
  UInt16.ofNat (x.toNat * 257)

def backgroundToRGB16 (background : PngBackground) : UInt16 × UInt16 × UInt16 :=
  match background with
  | .gray1 gray =>
      let gray16 := if gray then UInt16.ofNat uint16MaxValue else UInt16.ofNat 0
      (gray16, gray16, gray16)
  | .gray8 gray =>
      let gray16 := u8ToUInt16Full gray
      (gray16, gray16, gray16)
  | .rgb8 r g b => (u8ToUInt16Full r, u8ToUInt16Full g, u8ToUInt16Full b)
  | .gray16 gray => (gray, gray, gray)
  | .rgb16 r g b => (r, g, b)

def backgroundToGray16 (background : PngBackground) : UInt16 :=
  match background with
  | .gray1 gray => if gray then UInt16.ofNat uint16MaxValue else UInt16.ofNat 0
  | .gray8 gray => u8ToUInt16Full gray
  | .rgb8 r g b => UInt16.ofNat ((r.toNat * 257 + g.toNat * 257 + b.toNat * 257) / 3)
  | .gray16 gray => gray
  | .rgb16 r g b => UInt16.ofNat ((r.toNat + g.toNat + b.toNat) / 3)

def alphaCompositeByte (src bg alpha : UInt8) : UInt8 :=
  u8 ((src.toNat * alpha.toNat + bg.toNat * (255 - alpha.toNat)) / 255)

def alphaComposite16 (src bg alpha : UInt16) : UInt16 :=
  UInt16.ofNat ((src.toNat * alpha.toNat + bg.toNat * (uint16MaxValue - alpha.toNat)) / uint16MaxValue)

def alphaComposite16ToByte (src bg alpha : UInt16) : UInt8 :=
  u8 ((alphaComposite16 src bg alpha).toNat / 256)

def transparencyAlpha (trns : Option PngTransparency) (r g b : UInt8) : UInt8 :=
  match trns with
  | some (.gray1 gray) =>
      let gray8 := if gray then 0xff else 0
      if r == gray8 && g == gray8 && b == gray8 then u8 0 else u8 255
  | some (.gray8 gray) =>
      if r == gray && g == gray && b == gray then u8 0 else u8 255
  | some (.rgb8 tr tg tb) =>
      if r == tr && g == tg && b == tb then u8 0 else u8 255
  | some (.gray16 gray) =>
      let gray8 := u8 (gray.toNat / 256)
      if r == gray8 && g == gray8 && b == gray8 then u8 0 else u8 255
  | some (.rgb16 tr tg tb) =>
      if r == u8 (tr.toNat / 256) && g == u8 (tg.toNat / 256) &&
          b == u8 (tb.toNat / 256) then u8 0 else u8 255
  | none =>
      u8 255

def transparencyAlpha16 (trns : Option PngTransparency) (r g b : UInt16) : UInt16 :=
  match trns with
  | some (.gray1 gray) =>
      let gray16 := if gray then UInt16.ofNat uint16MaxValue else UInt16.ofNat 0
      if r == gray16 && g == gray16 && b == gray16 then UInt16.ofNat 0 else UInt16.ofNat uint16MaxValue
  | some (.gray8 gray) =>
      let gray16 := u8ToUInt16Full gray
      if r == gray16 && g == gray16 && b == gray16 then UInt16.ofNat 0 else UInt16.ofNat uint16MaxValue
  | some (.rgb8 tr tg tb) =>
      if r == u8ToUInt16Full tr && g == u8ToUInt16Full tg && b == u8ToUInt16Full tb then
        UInt16.ofNat 0
      else
        UInt16.ofNat uint16MaxValue
  | some (.gray16 gray) =>
      if r == gray && g == gray && b == gray then UInt16.ofNat 0 else UInt16.ofNat uint16MaxValue
  | some (.rgb16 tr tg tb) =>
      if r == tr && g == tg && b == tb then UInt16.ofNat 0 else UInt16.ofNat uint16MaxValue
  | none =>
      UInt16.ofNat uint16MaxValue

def decodeRowTrnsOverBackground
    (trns : PngTransparency) (background : PngBackground)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let (br, bg, bb) := backgroundToRGB background
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let r := row.get! base
      let g := if bpp == 1 then r else row.get! (base + 1)
      let b := if bpp == 1 then r else row.get! (base + 2)
      let (r, g, b) :=
        if transparencyAlpha (some trns) r g b == u8 0 then
          (br, bg, bb)
        else
          (r, g, b)
      let pixBase := (y * w + x) * bytesPerPixelRGB
      pixels := pixels.set! pixBase r
      pixels := pixels.set! (pixBase + 1) g
      pixels := pixels.set! (pixBase + 2) b
    return pixels

def decodeRowAlphaOverBackground
    (background : PngBackground) (row : ByteArray) (w y bpp : Nat)
    (pixels : ByteArray) : ByteArray :=
  Id.run do
    let (br, bg, bb) := backgroundToRGB background
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let r := row.get! base
      let g := if bpp == 2 then r else row.get! (base + 1)
      let b := if bpp == 2 then r else row.get! (base + 2)
      let a := if bpp == 4 then row.get! (base + 3)
        else if bpp == 2 then row.get! (base + 1)
        else u8 255
      let pixBase := (y * w + x) * bytesPerPixelRGB
      pixels := pixels.set! pixBase (alphaCompositeByte r br a)
      pixels := pixels.set! (pixBase + 1) (alphaCompositeByte g bg a)
      pixels := pixels.set! (pixBase + 2) (alphaCompositeByte b bb a)
    return pixels

def decodeRowGrayAlphaOverBackground
    (background : PngBackground) (row : ByteArray) (w y bpp : Nat)
    (pixels : ByteArray) : ByteArray :=
  Id.run do
    let bg := backgroundToGray background
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray := row.get! base
      let alpha := if bpp == 2 then row.get! (base + 1) else u8 255
      let pixBase := (y * w + x) * bytesPerPixelGray
      pixels := pixels.set! pixBase (alphaCompositeByte gray bg alpha)
    return pixels

def decodeRowAddAlpha (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let r := row.get! base
      let g := if bpp == 1 || bpp == 2 then r else row.get! (base + 1)
      let b := if bpp == 1 || bpp == 2 then r else row.get! (base + 2)
      let a := if bpp == 2 then row.get! (base + 1) else u8 255
      let pixBase := (y * w + x) * bytesPerPixelRGBA
      pixels := pixels.set! pixBase r
      pixels := pixels.set! (pixBase + 1) g
      pixels := pixels.set! (pixBase + 2) b
      pixels := pixels.set! (pixBase + 3) a
    return pixels

def decodeRowAddAlphaWithTransparency
    (trns : Option PngTransparency) (row : ByteArray) (w y bpp : Nat)
    (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let r := row.get! base
      let g := if bpp == 1 || bpp == 2 then r else row.get! (base + 1)
      let b := if bpp == 1 || bpp == 2 then r else row.get! (base + 2)
      let a := if bpp == 2 then row.get! (base + 1) else transparencyAlpha trns r g b
      let pixBase := (y * w + x) * bytesPerPixelRGBA
      pixels := pixels.set! pixBase r
      pixels := pixels.set! (pixBase + 1) g
      pixels := pixels.set! (pixBase + 2) b
      pixels := pixels.set! (pixBase + 3) a
    return pixels

def decodeRowGray (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let r := row.get! base
      let g := if bpp == 1 || bpp == 2 then r else row.get! (base + 1)
      let b := if bpp == 1 || bpp == 2 then r else row.get! (base + 2)
      let gray := u8 ((r.toNat + g.toNat + b.toNat) / 3)
      let pixBase := (y * w + x) * bytesPerPixelGray
      pixels := pixels.set! pixBase gray
    return pixels

def decodeRowGrayAlpha (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let r := row.get! base
      let g := if bpp == 1 || bpp == 2 then r else row.get! (base + 1)
      let b := if bpp == 1 || bpp == 2 then r else row.get! (base + 2)
      let gray := u8 ((r.toNat + g.toNat + b.toNat) / 3)
      let alpha := if bpp == 2 then row.get! (base + 1)
        else if bpp == 4 then row.get! (base + 3)
        else u8 255
      let pixBase := (y * w + x) * bytesPerPixelGrayAlpha
      pixels := pixels.set! pixBase gray
      pixels := pixels.set! (pixBase + 1) alpha
    return pixels

def decodeRowsLoopCore (raw : ByteArray) (w h bpp rowBytes outBpp : Nat)
    (convert : ByteArray -> Nat -> Nat -> Nat -> ByteArray -> ByteArray)
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
        if bpp == outBpp then
          let rowOffset := y * rowBytes
          row.copySlice 0 pixels rowOffset rowBytes
        else
          convert row w y bpp pixels
      decodeRowsLoopCore raw w h bpp rowBytes outBpp convert (y + 1) offset row pixels
    else
      none
  else
    return pixels
termination_by h - y
decreasing_by
  have hy : y < h := hlt
  have hy' : y < y + 1 := Nat.lt_succ_self y
  exact Nat.sub_lt_sub_left hy hy'

def decodeRowsLoopGray1Packed (raw : ByteArray) (w h : Nat) :
    Option ByteArray :=
  let rowBytes := gray1RowBytes w
  let pixels0 := ByteArray.mk <| Array.replicate (gray1DataSize w h) 0
  decodeRowsLoopCore raw w h 1 rowBytes 1 decodeRowGray 0 0 ByteArray.empty pixels0

def decodeRowsLoop (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGB decodeRowDropAlpha
    y offset prevRow pixels

def decodeRowsLoopTrnsOverBackground
    (trns : PngTransparency) (background : PngBackground)
    (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes 0
    (decodeRowTrnsOverBackground trns background) y offset prevRow pixels

def decodeRowsLoopAlphaOverBackground
    (background : PngBackground) (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes 0
    (decodeRowAlphaOverBackground background) y offset prevRow pixels

def decodeRowsLoopGrayAlphaOverBackground
    (background : PngBackground) (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes 0
    (decodeRowGrayAlphaOverBackground background) y offset prevRow pixels

def decodeRowsLoopRGBA (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGBA decodeRowAddAlpha
    y offset prevRow pixels

def decodeRowsLoopRGBAWithTransparency (trns : Option PngTransparency)
    (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGBA
    (decodeRowAddAlphaWithTransparency trns) y offset prevRow pixels

def decodeRowsLoopGray (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGray decodeRowGray
    y offset prevRow pixels

def decodeRowsLoopGrayAlpha (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGrayAlpha decodeRowGrayAlpha
    y offset prevRow pixels

@[inline] def rowU16High (row : ByteArray) (base : Nat) : UInt8 :=
  row.get! base

@[inline] def rowU16Low (row : ByteArray) (base : Nat) : UInt8 :=
  row.get! (base + 1)

@[inline] def rowU16Nat (row : ByteArray) (base : Nat) : Nat :=
  (rowU16High row base).toNat * 256 + (rowU16Low row base).toNat

@[inline] def setU16Bytes! (pixels : ByteArray) (base : Nat) (hi lo : UInt8) : ByteArray :=
  (pixels.set! base hi).set! (base + 1) lo

@[inline] def setU16Nat! (pixels : ByteArray) (base n : Nat) : ByteArray :=
  setU16Bytes! pixels base (u8 (n / 256)) (u8 n)

def decodeRowDropAlpha16 (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) :
    ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let rBase := base
      let gBase := if bpp == 2 || bpp == 4 then base else base + 2
      let bBase := if bpp == 2 || bpp == 4 then base else base + 4
      let pixBase := (y * w + x) * bytesPerPixelRGB16
      pixels := setU16Bytes! pixels pixBase (rowU16High row rBase) (rowU16Low row rBase)
      pixels := setU16Bytes! pixels (pixBase + 2) (rowU16High row gBase) (rowU16Low row gBase)
      pixels := setU16Bytes! pixels (pixBase + 4) (rowU16High row bBase) (rowU16Low row bBase)
    return pixels

def decodeRowAddAlpha16 (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) :
    ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let rBase := base
      let gBase := if bpp == 2 || bpp == 4 then base else base + 2
      let bBase := if bpp == 2 || bpp == 4 then base else base + 4
      let aBase? :=
        if bpp == 4 then some (base + 2) else if bpp == 8 then some (base + 6) else none
      let pixBase := (y * w + x) * bytesPerPixelRGBA16
      pixels := setU16Bytes! pixels pixBase (rowU16High row rBase) (rowU16Low row rBase)
      pixels := setU16Bytes! pixels (pixBase + 2) (rowU16High row gBase) (rowU16Low row gBase)
      pixels := setU16Bytes! pixels (pixBase + 4) (rowU16High row bBase) (rowU16Low row bBase)
      match aBase? with
      | some aBase =>
          pixels := setU16Bytes! pixels (pixBase + 6) (rowU16High row aBase) (rowU16Low row aBase)
      | none =>
          pixels := setU16Bytes! pixels (pixBase + 6) 0xff 0xff
    return pixels

def decodeRowGray16 (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray :=
        if bpp == 2 || bpp == 4 then
          rowU16Nat row base
        else
          (rowU16Nat row base + rowU16Nat row (base + 2) + rowU16Nat row (base + 4)) / 3
      let pixBase := (y * w + x) * bytesPerPixelGray16
      pixels := setU16Nat! pixels pixBase gray
    return pixels

def decodeRowGrayAlpha16 (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) :
    ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray :=
        if bpp == 2 || bpp == 4 then
          rowU16Nat row base
        else
          (rowU16Nat row base + rowU16Nat row (base + 2) + rowU16Nat row (base + 4)) / 3
      let alpha :=
        if bpp == 4 then
          rowU16Nat row (base + 2)
        else if bpp == 8 then
          rowU16Nat row (base + 6)
        else
          uint16MaxValue
      let pixBase := (y * w + x) * bytesPerPixelGrayAlpha16
      pixels := setU16Nat! pixels pixBase gray
      pixels := setU16Nat! pixels (pixBase + 2) alpha
    return pixels

def decodeRowsLoopRGB16 (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGB16 decodeRowDropAlpha16
    y offset prevRow pixels

def decodeRowsLoopRGBA16 (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGBA16 decodeRowAddAlpha16
    y offset prevRow pixels

def decodeRowsLoopGray16 (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGray16 decodeRowGray16
    y offset prevRow pixels

def decodeRowsLoopGrayAlpha16 (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGrayAlpha16 decodeRowGrayAlpha16
    y offset prevRow pixels

def decodeRowAddAlpha16WithTransparency
    (trns : Option PngTransparency) (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let grayLike := sourceColorType == 0 || sourceColorType == 4
      let r := UInt16.ofNat (rowU16Nat row base)
      let g := if grayLike then r else UInt16.ofNat (rowU16Nat row (base + 2))
      let b := if grayLike then r else UInt16.ofNat (rowU16Nat row (base + 4))
      let a :=
        if sourceColorType == 4 then
          UInt16.ofNat (rowU16Nat row (base + 2))
        else if sourceColorType == 6 then
          UInt16.ofNat (rowU16Nat row (base + 6))
        else
          transparencyAlpha16 trns r g b
      let pixBase := (y * w + x) * bytesPerPixelRGBA16
      pixels := setU16Nat! pixels pixBase r.toNat
      pixels := setU16Nat! pixels (pixBase + 2) g.toNat
      pixels := setU16Nat! pixels (pixBase + 4) b.toNat
      pixels := setU16Nat! pixels (pixBase + 6) a.toNat
    return pixels

def decodeRowsLoopRGBA16WithTransparency (trns : Option PngTransparency)
    (sourceColorType : Nat) (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGBA16
    (decodeRowAddAlpha16WithTransparency trns sourceColorType) y offset prevRow pixels

def decodeRowTrnsOverBackground16
    (trns : PngTransparency) (background : PngBackground) (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let (br, bg, bb) := backgroundToRGB16 background
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let grayLike := sourceColorType == 0 || sourceColorType == 4
      let r0 := UInt16.ofNat (rowU16Nat row base)
      let g0 := if grayLike then r0 else UInt16.ofNat (rowU16Nat row (base + 2))
      let b0 := if grayLike then r0 else UInt16.ofNat (rowU16Nat row (base + 4))
      let (r, g, b) :=
        if transparencyAlpha16 (some trns) r0 g0 b0 == UInt16.ofNat 0 then
          (br, bg, bb)
        else
          (r0, g0, b0)
      let pixBase := (y * w + x) * bytesPerPixelRGB16
      pixels := setU16Nat! pixels pixBase r.toNat
      pixels := setU16Nat! pixels (pixBase + 2) g.toNat
      pixels := setU16Nat! pixels (pixBase + 4) b.toNat
    return pixels

def decodeRowsLoopTrnsOverBackground16
    (trns : PngTransparency) (background : PngBackground) (sourceColorType : Nat)
    (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes 0
    (decodeRowTrnsOverBackground16 trns background sourceColorType) y offset prevRow pixels

def decodeRowAlphaOverBackground16
    (background : PngBackground) (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let (br, bg, bb) := backgroundToRGB16 background
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let grayLike := sourceColorType == 0 || sourceColorType == 4
      let r := UInt16.ofNat (rowU16Nat row base)
      let g := if grayLike then r else UInt16.ofNat (rowU16Nat row (base + 2))
      let b := if grayLike then r else UInt16.ofNat (rowU16Nat row (base + 4))
      let a :=
        if sourceColorType == 4 then
          UInt16.ofNat (rowU16Nat row (base + 2))
        else if sourceColorType == 6 then
          UInt16.ofNat (rowU16Nat row (base + 6))
        else
          UInt16.ofNat uint16MaxValue
      let pixBase := (y * w + x) * bytesPerPixelRGB16
      pixels := setU16Nat! pixels pixBase (alphaComposite16 r br a).toNat
      pixels := setU16Nat! pixels (pixBase + 2) (alphaComposite16 g bg a).toNat
      pixels := setU16Nat! pixels (pixBase + 4) (alphaComposite16 b bb a).toNat
    return pixels

def decodeRowsLoopAlphaOverBackground16
    (background : PngBackground) (sourceColorType : Nat)
    (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGB16
    (decodeRowAlphaOverBackground16 background sourceColorType) y offset prevRow pixels

def decodeRowGrayAlphaOverBackground16
    (background : PngBackground) (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let bg := backgroundToGray16 background
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray :=
        if sourceColorType == 0 || sourceColorType == 4 then
          UInt16.ofNat (rowU16Nat row base)
        else
          UInt16.ofNat
            ((rowU16Nat row base + rowU16Nat row (base + 2) + rowU16Nat row (base + 4)) / 3)
      let alpha :=
        if sourceColorType == 4 then
          UInt16.ofNat (rowU16Nat row (base + 2))
        else if sourceColorType == 6 then
          UInt16.ofNat (rowU16Nat row (base + 6))
        else
          UInt16.ofNat uint16MaxValue
      let pixBase := (y * w + x) * bytesPerPixelGray16
      pixels := setU16Nat! pixels pixBase (alphaComposite16 gray bg alpha).toNat
    return pixels

def decodeRowsLoopGrayAlphaOverBackground16
    (background : PngBackground) (sourceColorType : Nat)
    (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGray16
    (decodeRowGrayAlphaOverBackground16 background sourceColorType) y offset prevRow pixels

def decodeRowDown16ToRGBA8WithTransparency
    (trns : Option PngTransparency) (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let grayLike := sourceColorType == 0 || sourceColorType == 4
      let r16 := UInt16.ofNat (rowU16Nat row base)
      let g16 := if grayLike then r16 else UInt16.ofNat (rowU16Nat row (base + 2))
      let b16 := if grayLike then r16 else UInt16.ofNat (rowU16Nat row (base + 4))
      let a :=
        if sourceColorType == 4 then
          rowU16High row (base + 2)
        else if sourceColorType == 6 then
          rowU16High row (base + 6)
        else if transparencyAlpha16 trns r16 g16 b16 == UInt16.ofNat 0 then
          u8 0
        else
          u8 255
      let pixBase := (y * w + x) * bytesPerPixelRGBA
      pixels := pixels.set! pixBase (u8 (r16.toNat / 256))
      pixels := pixels.set! (pixBase + 1) (u8 (g16.toNat / 256))
      pixels := pixels.set! (pixBase + 2) (u8 (b16.toNat / 256))
      pixels := pixels.set! (pixBase + 3) a
    return pixels

def decodeRowsLoopDown16ToRGBA8WithTransparency (trns : Option PngTransparency)
    (sourceColorType : Nat) (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGBA
    (decodeRowDown16ToRGBA8WithTransparency trns sourceColorType) y offset prevRow pixels

def decodeRowDown16TrnsOverBackgroundRGB8
    (trns : PngTransparency) (background : PngBackground) (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let (br, bg, bb) := backgroundToRGB16 background
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let grayLike := sourceColorType == 0 || sourceColorType == 4
      let r0 := UInt16.ofNat (rowU16Nat row base)
      let g0 := if grayLike then r0 else UInt16.ofNat (rowU16Nat row (base + 2))
      let b0 := if grayLike then r0 else UInt16.ofNat (rowU16Nat row (base + 4))
      let (r, g, b) :=
        if transparencyAlpha16 (some trns) r0 g0 b0 == UInt16.ofNat 0 then
          (br, bg, bb)
        else
          (r0, g0, b0)
      let pixBase := (y * w + x) * bytesPerPixelRGB
      pixels := pixels.set! pixBase (u8 (r.toNat / 256))
      pixels := pixels.set! (pixBase + 1) (u8 (g.toNat / 256))
      pixels := pixels.set! (pixBase + 2) (u8 (b.toNat / 256))
    return pixels

def decodeRowsLoopDown16TrnsOverBackgroundRGB8
    (trns : PngTransparency) (background : PngBackground) (sourceColorType : Nat)
    (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGB
    (decodeRowDown16TrnsOverBackgroundRGB8 trns background sourceColorType) y offset prevRow pixels

def decodeRowDown16AlphaOverBackgroundRGB8
    (background : PngBackground) (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let (br, bg, bb) := backgroundToRGB16 background
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let grayLike := sourceColorType == 0 || sourceColorType == 4
      let r := UInt16.ofNat (rowU16Nat row base)
      let g := if grayLike then r else UInt16.ofNat (rowU16Nat row (base + 2))
      let b := if grayLike then r else UInt16.ofNat (rowU16Nat row (base + 4))
      let a :=
        if sourceColorType == 4 then
          UInt16.ofNat (rowU16Nat row (base + 2))
        else if sourceColorType == 6 then
          UInt16.ofNat (rowU16Nat row (base + 6))
        else
          UInt16.ofNat uint16MaxValue
      let pixBase := (y * w + x) * bytesPerPixelRGB
      pixels := pixels.set! pixBase (alphaComposite16ToByte r br a)
      pixels := pixels.set! (pixBase + 1) (alphaComposite16ToByte g bg a)
      pixels := pixels.set! (pixBase + 2) (alphaComposite16ToByte b bb a)
    return pixels

def decodeRowsLoopDown16AlphaOverBackgroundRGB8
    (background : PngBackground) (sourceColorType : Nat)
    (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGB
    (decodeRowDown16AlphaOverBackgroundRGB8 background sourceColorType) y offset prevRow pixels

def decodeRowDown16GrayAlphaOverBackgroundGray8
    (background : PngBackground) (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let bg := backgroundToGray16 background
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray :=
        if sourceColorType == 0 || sourceColorType == 4 then
          UInt16.ofNat (rowU16Nat row base)
        else
          UInt16.ofNat
            ((rowU16Nat row base + rowU16Nat row (base + 2) + rowU16Nat row (base + 4)) / 3)
      let alpha :=
        if sourceColorType == 4 then
          UInt16.ofNat (rowU16Nat row (base + 2))
        else if sourceColorType == 6 then
          UInt16.ofNat (rowU16Nat row (base + 6))
        else
          UInt16.ofNat uint16MaxValue
      let pixBase := (y * w + x) * bytesPerPixelGray
      pixels := pixels.set! pixBase (alphaComposite16ToByte gray bg alpha)
    return pixels

def decodeRowsLoopDown16GrayAlphaOverBackgroundGray8
    (background : PngBackground) (sourceColorType : Nat)
    (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGray
    (decodeRowDown16GrayAlphaOverBackgroundGray8 background sourceColorType) y offset prevRow pixels

def decodeRowDown16ToRGB8 (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let grayLike := sourceColorType == 0 || sourceColorType == 4
      let r := rowU16High row base
      let g := if grayLike then r else rowU16High row (base + 2)
      let b := if grayLike then r else rowU16High row (base + 4)
      let pixBase := (y * w + x) * bytesPerPixelRGB
      pixels := pixels.set! pixBase r
      pixels := pixels.set! (pixBase + 1) g
      pixels := pixels.set! (pixBase + 2) b
    return pixels

def decodeRowDown16ToRGBA8 (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let grayLike := sourceColorType == 0 || sourceColorType == 4
      let r := rowU16High row base
      let g := if grayLike then r else rowU16High row (base + 2)
      let b := if grayLike then r else rowU16High row (base + 4)
      let a :=
        if sourceColorType == 4 then
          rowU16High row (base + 2)
        else if sourceColorType == 6 then
          rowU16High row (base + 6)
        else
          0xff
      let pixBase := (y * w + x) * bytesPerPixelRGBA
      pixels := pixels.set! pixBase r
      pixels := pixels.set! (pixBase + 1) g
      pixels := pixels.set! (pixBase + 2) b
      pixels := pixels.set! (pixBase + 3) a
    return pixels

def decodeRowDown16ToGray8 (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray :=
        if sourceColorType == 0 || sourceColorType == 4 then
          rowU16High row base
        else
          u8 (((rowU16High row base).toNat +
            (rowU16High row (base + 2)).toNat +
            (rowU16High row (base + 4)).toNat) / 3)
      let pixBase := (y * w + x) * bytesPerPixelGray
      pixels := pixels.set! pixBase gray
    return pixels

def decodeRowDown16ToGrayAlpha8 (sourceColorType : Nat)
    (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray :=
        if sourceColorType == 0 || sourceColorType == 4 then
          rowU16High row base
        else
          u8 (((rowU16High row base).toNat +
            (rowU16High row (base + 2)).toNat +
            (rowU16High row (base + 4)).toNat) / 3)
      let alpha :=
        if sourceColorType == 4 then
          rowU16High row (base + 2)
        else if sourceColorType == 6 then
          rowU16High row (base + 6)
        else
          0xff
      let pixBase := (y * w + x) * bytesPerPixelGrayAlpha
      pixels := pixels.set! pixBase gray
      pixels := pixels.set! (pixBase + 1) alpha
    return pixels

def decodeRowsLoopDown16To8 (targetColorType : UInt8) (sourceColorType : Nat)
    (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  if targetColorType == u8 0 then
    decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGray
      (decodeRowDown16ToGray8 sourceColorType) y offset prevRow pixels
  else if targetColorType == u8 2 then
    decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGB
      (decodeRowDown16ToRGB8 sourceColorType) y offset prevRow pixels
  else if targetColorType == u8 4 then
    decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGrayAlpha
      (decodeRowDown16ToGrayAlpha8 sourceColorType) y offset prevRow pixels
  else if targetColorType == u8 6 then
    decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGBA
      (decodeRowDown16ToRGBA8 sourceColorType) y offset prevRow pixels
  else
    none

@[inline] def clamp01 (x : Float) : Float :=
  if x <= 0.0 then
    0.0
  else if x >= 1.0 then
    1.0
  else
    x

@[inline] def linearToSrgb (linear : Float) : Float :=
  let linear := clamp01 linear
  if linear <= 0.0031308 then
    12.92 * linear
  else
    1.055 * Float.pow linear (1.0 / 2.4) - 0.055

@[inline] def roundedUnitToNat (x : Float) (maxValue : Nat) : Nat :=
  let scaled := clamp01 x * Float.ofNat maxValue + 0.5
  if scaled <= 0.0 then
    0
  else if scaled >= Float.ofNat maxValue then
    maxValue
  else
    (Float.floor scaled).toUInt64.toNat

@[inline] def gammaSampleToSrgbNat (gammaScaled sample maxValue : Nat) : Nat :=
  if gammaScaled == 0 then
    sample
  else if maxValue == 0 then
    0
  else
    let gamma := Float.ofNat gammaScaled / 100000.0
    let encoded := Float.ofNat sample / Float.ofNat maxValue
    let linear := Float.pow (clamp01 encoded) (1.0 / gamma)
    roundedUnitToNat (linearToSrgb linear) maxValue

def gammaToSrgb8Lut (gammaScaled : Nat) : Array UInt8 :=
  Id.run do
    let mut lut : Array UInt8 := Array.empty
    for n in [0:256] do
      lut := lut.push (u8 (gammaSampleToSrgbNat gammaScaled n 255))
    return lut

def gammaToSrgb16Lut (gammaScaled : Nat) : Array UInt16 :=
  Id.run do
    let mut lut : Array UInt16 := Array.empty
    for n in [0:65536] do
      lut := lut.push (UInt16.ofNat (gammaSampleToSrgbNat gammaScaled n uint16MaxValue))
    return lut

def applyGamma8ToPixels (gammaScaled : Nat) (colorType : UInt8)
    (pixels : ByteArray) : Option ByteArray := do
  let stride ← pngBytesPerPixelForColorTypeAndBitDepth? colorType.toNat 8
  if stride == 0 || pixels.size % stride != 0 then
    none
  let lut := gammaToSrgb8Lut gammaScaled
  let count := pixels.size / stride
  let out :=
    Id.run do
      let mut out := pixels
      for i in [0:count] do
        let base := i * stride
        out := out.set! base lut[(pixels.get! base).toNat]!
        if colorType == u8 2 || colorType == u8 6 then
          out := out.set! (base + 1) lut[(pixels.get! (base + 1)).toNat]!
          out := out.set! (base + 2) lut[(pixels.get! (base + 2)).toNat]!
      return out
  some out

def applyGamma16ToPixels (gammaScaled : Nat) (colorType : UInt8)
    (pixels : ByteArray) : Option ByteArray := do
  let stride ← pngBytesPerPixelForColorTypeAndBitDepth? colorType.toNat 16
  if stride == 0 || pixels.size % stride != 0 then
    none
  let lut := gammaToSrgb16Lut gammaScaled
  let count := pixels.size / stride
  let out :=
    Id.run do
      let mut out := pixels
      for i in [0:count] do
        let base := i * stride
        let r := lut[rowU16Nat pixels base]!
        out := setU16Nat! out base r.toNat
        if colorType == u8 2 || colorType == u8 6 then
          let g := lut[rowU16Nat pixels (base + 2)]!
          let b := lut[rowU16Nat pixels (base + 4)]!
          out := setU16Nat! out (base + 2) g.toNat
          out := setU16Nat! out (base + 4) b.toNat
      return out
  some out

structure PngMatrix3 where
  m00 : Float
  m01 : Float
  m02 : Float
  m10 : Float
  m11 : Float
  m12 : Float
  m20 : Float
  m21 : Float
  m22 : Float
deriving Repr

def PngMatrix3.mulVec (m : PngMatrix3) (x y z : Float) : Float × Float × Float :=
  (m.m00 * x + m.m01 * y + m.m02 * z,
   m.m10 * x + m.m11 * y + m.m12 * z,
   m.m20 * x + m.m21 * y + m.m22 * z)

def PngMatrix3.mul (a b : PngMatrix3) : PngMatrix3 :=
  { m00 := a.m00 * b.m00 + a.m01 * b.m10 + a.m02 * b.m20
    m01 := a.m00 * b.m01 + a.m01 * b.m11 + a.m02 * b.m21
    m02 := a.m00 * b.m02 + a.m01 * b.m12 + a.m02 * b.m22
    m10 := a.m10 * b.m00 + a.m11 * b.m10 + a.m12 * b.m20
    m11 := a.m10 * b.m01 + a.m11 * b.m11 + a.m12 * b.m21
    m12 := a.m10 * b.m02 + a.m11 * b.m12 + a.m12 * b.m22
    m20 := a.m20 * b.m00 + a.m21 * b.m10 + a.m22 * b.m20
    m21 := a.m20 * b.m01 + a.m21 * b.m11 + a.m22 * b.m21
    m22 := a.m20 * b.m02 + a.m21 * b.m12 + a.m22 * b.m22 }

def PngMatrix3.det (m : PngMatrix3) : Float :=
  m.m00 * (m.m11 * m.m22 - m.m12 * m.m21) -
  m.m01 * (m.m10 * m.m22 - m.m12 * m.m20) +
  m.m02 * (m.m10 * m.m21 - m.m11 * m.m20)

def PngMatrix3.inverse? (m : PngMatrix3) : Option PngMatrix3 :=
  let det := m.det
  if det == 0.0 then
    none
  else
    some
      { m00 := (m.m11 * m.m22 - m.m12 * m.m21) / det
        m01 := (m.m02 * m.m21 - m.m01 * m.m22) / det
        m02 := (m.m01 * m.m12 - m.m02 * m.m11) / det
        m10 := (m.m12 * m.m20 - m.m10 * m.m22) / det
        m11 := (m.m00 * m.m22 - m.m02 * m.m20) / det
        m12 := (m.m02 * m.m10 - m.m00 * m.m12) / det
        m20 := (m.m10 * m.m21 - m.m11 * m.m20) / det
        m21 := (m.m01 * m.m20 - m.m00 * m.m21) / det
        m22 := (m.m00 * m.m11 - m.m01 * m.m10) / det }

def PngChromaticityPoint.toXyz? (p : PngChromaticityPoint) :
    Option (Float × Float × Float) :=
  let x := Float.ofInt p.x / 100000.0
  let y := Float.ofInt p.y / 100000.0
  if y == 0.0 then
    none
  else
    some (x / y, 1.0, (1.0 - x - y) / y)

def PngChromaticities.rgbToXyz? (c : PngChromaticities) : Option PngMatrix3 := do
  let (xw, yw, zw) ← c.white.toXyz?
  let (xr, yr, zr) ← c.red.toXyz?
  let (xg, yg, zg) ← c.green.toXyz?
  let (xb, yb, zb) ← c.blue.toXyz?
  let primary : PngMatrix3 :=
    { m00 := xr, m01 := xg, m02 := xb
      m10 := yr, m11 := yg, m12 := yb
      m20 := zr, m21 := zg, m22 := zb }
  let inv ← primary.inverse?
  let (sr, sg, sb) := inv.mulVec xw yw zw
  some
    { m00 := xr * sr, m01 := xg * sg, m02 := xb * sb
      m10 := yr * sr, m11 := yg * sg, m12 := yb * sb
      m20 := zr * sr, m21 := zg * sg, m22 := zb * sb }

def bradfordMatrix : PngMatrix3 :=
  { m00 := 0.8951, m01 := 0.2664, m02 := -0.1614
    m10 := -0.7502, m11 := 1.7135, m12 := 0.0367
    m20 := 0.0389, m21 := -0.0685, m22 := 1.0296 }

def bradfordInverseMatrix : PngMatrix3 :=
  { m00 := 0.9869929, m01 := -0.1470543, m02 := 0.1599627
    m10 := 0.4323053, m11 := 0.5183603, m12 := 0.0492912
    m20 := -0.0085287, m21 := 0.0400428, m22 := 0.9684867 }

def srgbXyzToRgbMatrix : PngMatrix3 :=
  { m00 := 3.2404542, m01 := -1.5371385, m02 := -0.4985314
    m10 := -0.9692660, m11 := 1.8760108, m12 := 0.0415560
    m20 := 0.0556434, m21 := -0.2040259, m22 := 1.0572252 }

def bradfordAdaptationMatrix? (sourceWhite targetWhite : Float × Float × Float) :
    Option PngMatrix3 := do
  let (sx, sy, sz) := sourceWhite
  let (tx, ty, tz) := targetWhite
  let (sl, sm, ss) := bradfordMatrix.mulVec sx sy sz
  let (tl, tm, ts) := bradfordMatrix.mulVec tx ty tz
  if sl == 0.0 || sm == 0.0 || ss == 0.0 then
    none
  else
    let scale : PngMatrix3 :=
      { m00 := tl / sl, m01 := 0.0, m02 := 0.0
        m10 := 0.0, m11 := tm / sm, m12 := 0.0
        m20 := 0.0, m21 := 0.0, m22 := ts / ss }
    some (bradfordInverseMatrix.mul (scale.mul bradfordMatrix))

def PngChromaticities.sourceToSrgbMatrix? (c : PngChromaticities) :
    Option PngMatrix3 := do
  let rgbToXyz ← c.rgbToXyz?
  let sourceWhite ← c.white.toXyz?
  let targetWhite ← PngChromaticities.srgb.white.toXyz?
  let adapt ← bradfordAdaptationMatrix? sourceWhite targetWhite
  some (srgbXyzToRgbMatrix.mul (adapt.mul rgbToXyz))

@[inline] def sourceSampleToLinear (gamma : Option Nat) (sample maxValue : Nat) : Float :=
  if maxValue == 0 then
    0.0
  else
    let encoded := Float.ofNat sample / Float.ofNat maxValue
    match gamma with
    | some gammaScaled =>
        if gammaScaled == 0 then
          clamp01 encoded
        else
          Float.pow (clamp01 encoded) (1.0 / (Float.ofNat gammaScaled / 100000.0))
    | none =>
        clamp01 encoded

@[inline] def chrmRgbToLinearSrgb (matrix : PngMatrix3) (gamma : Option Nat)
    (r g b maxValue : Nat) : Float × Float × Float :=
  let rl := sourceSampleToLinear gamma r maxValue
  let gl := sourceSampleToLinear gamma g maxValue
  let bl := sourceSampleToLinear gamma b maxValue
  matrix.mulVec rl gl bl

@[inline] def chrmRgbToSrgbNat (matrix : PngMatrix3) (gamma : Option Nat)
    (r g b maxValue : Nat) : Nat × Nat × Nat :=
  let (rl, gl, bl) := chrmRgbToLinearSrgb matrix gamma r g b maxValue
  (roundedUnitToNat (linearToSrgb rl) maxValue,
   roundedUnitToNat (linearToSrgb gl) maxValue,
   roundedUnitToNat (linearToSrgb bl) maxValue)

@[inline] def chrmRgbToGrayNat (matrix : PngMatrix3) (gamma : Option Nat)
    (r g b maxValue : Nat) : Nat :=
  let (rl, gl, bl) := chrmRgbToLinearSrgb matrix gamma r g b maxValue
  let y := 0.2126 * clamp01 rl + 0.7152 * clamp01 gl + 0.0722 * clamp01 bl
  roundedUnitToNat (linearToSrgb y) maxValue

def applyChrm8ToPixels (matrix : PngMatrix3) (gamma : Option Nat) (colorType : UInt8)
    (pixels : ByteArray) : Option ByteArray := do
  let stride ← pngBytesPerPixelForColorTypeAndBitDepth? colorType.toNat 8
  if stride == 0 || pixels.size % stride != 0 then
    none
  if colorType != u8 2 && colorType != u8 6 then
    some pixels
  else
    let count := pixels.size / stride
    let out :=
      Id.run do
        let mut out := pixels
        for i in [0:count] do
          let base := i * stride
          let (r, g, b) := chrmRgbToSrgbNat matrix gamma
            (pixels.get! base).toNat (pixels.get! (base + 1)).toNat
            (pixels.get! (base + 2)).toNat 255
          out := out.set! base (u8 r)
          out := out.set! (base + 1) (u8 g)
          out := out.set! (base + 2) (u8 b)
        return out
    some out

def applyChrm16ToPixels (matrix : PngMatrix3) (gamma : Option Nat) (colorType : UInt8)
    (pixels : ByteArray) : Option ByteArray := do
  let stride ← pngBytesPerPixelForColorTypeAndBitDepth? colorType.toNat 16
  if stride == 0 || pixels.size % stride != 0 then
    none
  if colorType != u8 2 && colorType != u8 6 then
    some pixels
  else
    let count := pixels.size / stride
    let out :=
      Id.run do
        let mut out := pixels
        for i in [0:count] do
          let base := i * stride
          let (r, g, b) := chrmRgbToSrgbNat matrix gamma
            (rowU16Nat pixels base) (rowU16Nat pixels (base + 2))
            (rowU16Nat pixels (base + 4)) uint16MaxValue
          out := setU16Nat! out base r
          out := setU16Nat! out (base + 2) g
          out := setU16Nat! out (base + 4) b
        return out
    some out

def applyPngColorSpaceTransform (metadata : PngMetadata) (sourceColorType : Nat)
    (targetColorType targetBitDepth : UInt8) (pixels : ByteArray) : Option ByteArray :=
  match metadata.srgb with
  | some _ => some pixels
  | none =>
      match metadata.chromaticities with
      | some chromaticities =>
          if sourceColorType == 2 || sourceColorType == 6 then
            match chromaticities.sourceToSrgbMatrix? with
            | none => none
            | some matrix =>
                if targetBitDepth == u8 8 then
                  applyChrm8ToPixels matrix metadata.gamma targetColorType pixels
                else if targetBitDepth == u8 16 then
                  applyChrm16ToPixels matrix metadata.gamma targetColorType pixels
                else
                  some pixels
          else
            match metadata.gamma with
            | none => some pixels
            | some gamma =>
                if targetBitDepth == u8 8 then
                  applyGamma8ToPixels gamma targetColorType pixels
                else if targetBitDepth == u8 16 then
                  applyGamma16ToPixels gamma targetColorType pixels
                else
                  some pixels
      | none =>
          match metadata.gamma with
          | none => some pixels
          | some gamma =>
              if targetBitDepth == u8 8 then
                applyGamma8ToPixels gamma targetColorType pixels
              else if targetBitDepth == u8 16 then
                applyGamma16ToPixels gamma targetColorType pixels
              else
                some pixels

def decodeRowChrmToGray8 (matrix : PngMatrix3) (gamma : Option Nat)
    (row : ByteArray) (w y bpp : Nat)
    (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray := chrmRgbToGrayNat matrix gamma
        (row.get! base).toNat (row.get! (base + 1)).toNat
        (row.get! (base + 2)).toNat 255
      let pixBase := (y * w + x) * bytesPerPixelGray
      pixels := pixels.set! pixBase (u8 gray)
    return pixels

def decodeRowChrmToGrayAlpha8 (matrix : PngMatrix3) (gamma : Option Nat)
    (sourceColorType : Nat) (row : ByteArray) (w y bpp : Nat)
    (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray := chrmRgbToGrayNat matrix gamma
        (row.get! base).toNat (row.get! (base + 1)).toNat
        (row.get! (base + 2)).toNat 255
      let alpha := if sourceColorType == 6 then row.get! (base + 3) else u8 255
      let pixBase := (y * w + x) * bytesPerPixelGrayAlpha
      pixels := pixels.set! pixBase (u8 gray)
      pixels := pixels.set! (pixBase + 1) alpha
    return pixels

def decodeRowChrmToGray16 (matrix : PngMatrix3) (gamma : Option Nat)
    (row : ByteArray) (w y bpp : Nat)
    (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray := chrmRgbToGrayNat matrix gamma
        (rowU16Nat row base) (rowU16Nat row (base + 2))
        (rowU16Nat row (base + 4)) uint16MaxValue
      let pixBase := (y * w + x) * bytesPerPixelGray16
      pixels := setU16Nat! pixels pixBase gray
    return pixels

def decodeRowChrmToGrayAlpha16 (matrix : PngMatrix3) (gamma : Option Nat)
    (sourceColorType : Nat) (row : ByteArray) (w y bpp : Nat)
    (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray := chrmRgbToGrayNat matrix gamma
        (rowU16Nat row base) (rowU16Nat row (base + 2))
        (rowU16Nat row (base + 4)) uint16MaxValue
      let alpha := if sourceColorType == 6 then rowU16Nat row (base + 6) else uint16MaxValue
      let pixBase := (y * w + x) * bytesPerPixelGrayAlpha16
      pixels := setU16Nat! pixels pixBase gray
      pixels := setU16Nat! pixels (pixBase + 2) alpha
    return pixels

def decodeRowChrmDown16ToGray8 (matrix : PngMatrix3) (gamma : Option Nat)
    (row : ByteArray) (w y bpp : Nat)
    (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray := chrmRgbToGrayNat matrix gamma
        (rowU16Nat row base) (rowU16Nat row (base + 2))
        (rowU16Nat row (base + 4)) uint16MaxValue
      let pixBase := (y * w + x) * bytesPerPixelGray
      pixels := pixels.set! pixBase (u8 (gray / 256))
    return pixels

def decodeRowChrmDown16ToGrayAlpha8 (matrix : PngMatrix3) (gamma : Option Nat)
    (sourceColorType : Nat) (row : ByteArray) (w y bpp : Nat)
    (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let gray := chrmRgbToGrayNat matrix gamma
        (rowU16Nat row base) (rowU16Nat row (base + 2))
        (rowU16Nat row (base + 4)) uint16MaxValue
      let alpha := if sourceColorType == 6 then rowU16High row (base + 6) else u8 255
      let pixBase := (y * w + x) * bytesPerPixelGrayAlpha
      pixels := pixels.set! pixBase (u8 (gray / 256))
      pixels := pixels.set! (pixBase + 1) alpha
    return pixels

def decodeRowsLoopChrmToGrayTarget (matrix : PngMatrix3) (gamma : Option Nat)
    (targetColorType : UInt8) (sourceColorType : Nat) (source16 target8 target16 : Bool)
    (raw : ByteArray) (w h bpp rowBytes : Nat) (pixels0 : ByteArray) : Option ByteArray :=
  if targetColorType == u8 0 then
    if source16 && target8 then
      decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGray
        (decodeRowChrmDown16ToGray8 matrix gamma) 0 0 ByteArray.empty pixels0
    else if source16 && target16 then
      decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGray16
        (decodeRowChrmToGray16 matrix gamma) 0 0 ByteArray.empty pixels0
    else
      decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGray
        (decodeRowChrmToGray8 matrix gamma) 0 0 ByteArray.empty pixels0
  else if targetColorType == u8 4 then
    if source16 && target8 then
      decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGrayAlpha
        (decodeRowChrmDown16ToGrayAlpha8 matrix gamma sourceColorType) 0 0 ByteArray.empty pixels0
    else if source16 && target16 then
      decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGrayAlpha16
        (decodeRowChrmToGrayAlpha16 matrix gamma sourceColorType) 0 0 ByteArray.empty pixels0
    else
      decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGrayAlpha
        (decodeRowChrmToGrayAlpha8 matrix gamma sourceColorType) 0 0 ByteArray.empty pixels0
  else
    none

class PngPixel (α : Type u) [Pixel α] where
  encodeRaw : Bitmap α -> ByteArray
  colorType : UInt8
  bitDepth : UInt8
  decodeRowsLoop : (raw : ByteArray) -> (w h bpp rowBytes : Nat) ->
    (y offset : Nat) -> (prevRow pixels : ByteArray) -> Option ByteArray

def decodeParsedBitmapWithMetadata {px : Type u} [Pixel px] [PngPixel px]
    (parsed : PngParsed) : Option (PngDecodeResult px) := do
  let hdr := parsed.header
  let idat := parsed.idat
  if !pngColorTypeBitDepthSupported hdr.colorType hdr.bitDepth then
    none
  if hdr.colorType != 0 && hdr.colorType != 2 && hdr.colorType != 4 &&
      hdr.colorType != 6 then
    none
  let targetColorType := PngPixel.colorType (α := px)
  let targetBitDepth := PngPixel.bitDepth (α := px)
  let source1 := hdr.bitDepth == 1
  let source16 := hdr.bitDepth == 16
  let target8 := targetBitDepth == u8 8
  let target16 := targetBitDepth == u8 16
  let bitDepthCompatible :=
    hdr.bitDepth == targetBitDepth.toNat ||
      (source16 && target8) ||
      (source1 && (target8 || target16))
  if !bitDepthCompatible then
    none
  let inflated ←
    if hsize : 2 <= idat.size then
      match zlibDecompressStored idat hsize with
      | some raw => some raw
      | none => zlibDecompress idat hsize
    else
      none
  let (raw, bpp, rowBytes) ←
    if source1 then
      let packedRowBytes := gray1RowBytes hdr.width
      let packedRaw ← normalizeGray1RawByInterlace? inflated hdr
      let expected := hdr.height * (packedRowBytes + 1)
      if packedRaw.size != expected then
        none
      let flat ← decodeRowsLoopGray1Packed packedRaw hdr.width hdr.height
      let virtualBitDepth := if target16 then 16 else 8
      let raw := gray1FlatToSampleRaw flat hdr.width hdr.height virtualBitDepth
      let bpp := if target16 then 2 else 1
      let rowBytes := hdr.width * bpp
      some (raw, bpp, rowBytes)
    else
      let bpp ← pngBytesPerPixelForColorTypeAndBitDepth? hdr.colorType hdr.bitDepth
      let rowBytes := hdr.width * bpp
      let raw ← normalizeRawByInterlace? inflated hdr bpp
      let expected := hdr.height * (rowBytes + 1)
      if raw.size != expected then
        none
      some (raw, bpp, rowBytes)
  let totalBytes := hdr.width * hdr.height * Pixel.bytesPerPixel (α := px)
  let pixels0 := ByteArray.mk <| Array.replicate totalBytes 0
  let chrmGrayActive :=
    parsed.metadata.srgb.isNone && parsed.metadata.chromaticities.isSome &&
    (hdr.colorType == 2 || hdr.colorType == 6) &&
    (targetColorType == u8 0 || targetColorType == u8 4)
  let decodeDefaultRows : Option ByteArray :=
    if chrmGrayActive then
      match parsed.metadata.chromaticities with
      | some chromaticities =>
          match chromaticities.sourceToSrgbMatrix? with
          | some matrix =>
              decodeRowsLoopChrmToGrayTarget matrix parsed.metadata.gamma targetColorType
                hdr.colorType source16 target8 target16 raw hdr.width hdr.height bpp rowBytes pixels0
          | none => none
      | none => none
    else if source16 && target8 then
      decodeRowsLoopDown16To8 targetColorType hdr.colorType
        raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
    else
      PngPixel.decodeRowsLoop (α := px)
        raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
  let pixels ←
    match parsed.metadata.transparency with
    | some trns =>
        if targetColorType == u8 6 then
          if source16 && target8 then
            decodeRowsLoopDown16ToRGBA8WithTransparency (some trns) hdr.colorType
              raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
          else if source16 && target16 then
            decodeRowsLoopRGBA16WithTransparency (some trns) hdr.colorType
              raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
          else
            decodeRowsLoopRGBAWithTransparency (some trns)
              raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
        else if targetColorType == u8 2 then
          match parsed.metadata.background with
          | some background =>
              if source16 && target8 then
                decodeRowsLoopDown16TrnsOverBackgroundRGB8 trns background hdr.colorType
                  raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
              else if source16 && target16 then
                decodeRowsLoopTrnsOverBackground16 trns background hdr.colorType
                  raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
              else
                decodeRowsLoopTrnsOverBackground trns background
                  raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
          | none =>
              none
        else
          none
    | none =>
        if hdr.colorType == 4 &&
            (targetColorType == u8 2 || targetColorType == u8 0) then
          match parsed.metadata.background with
          | some background =>
              if targetColorType == u8 2 then
                if source16 && target8 then
                  decodeRowsLoopDown16AlphaOverBackgroundRGB8 background hdr.colorType
                    raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
                else if source16 && target16 then
                  decodeRowsLoopAlphaOverBackground16 background hdr.colorType
                    raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
                else
                  decodeRowsLoopAlphaOverBackground background
                    raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
              else
                if source16 && target8 then
                  decodeRowsLoopDown16GrayAlphaOverBackgroundGray8 background hdr.colorType
                    raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
                else if source16 && target16 then
                  decodeRowsLoopGrayAlphaOverBackground16 background hdr.colorType
                    raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
                else
                  decodeRowsLoopGrayAlphaOverBackground background
                    raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
          | none =>
              none
        else if hdr.colorType == 6 && targetColorType == u8 2 then
          match parsed.metadata.background with
          | some background =>
              if source16 && target8 then
                decodeRowsLoopDown16AlphaOverBackgroundRGB8 background hdr.colorType
                  raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
              else if source16 && target16 then
                decodeRowsLoopAlphaOverBackground16 background hdr.colorType
                  raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
              else
                decodeRowsLoopAlphaOverBackground background
                  raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
          | none =>
              decodeDefaultRows
        else
          decodeDefaultRows
  let pixels ← applyPngColorSpaceTransform parsed.metadata hdr.colorType
    targetColorType targetBitDepth pixels
  let size : Size := { width := hdr.width, height := hdr.height }
  if hsize : pixels.size = size.width * size.height * Pixel.bytesPerPixel (α := px) then
    some
      { bitmap := { size, data := pixels, valid := hsize }
        metadata := parsed.metadata }
  else
    none

def decodeBitmapWithMetadata {px : Type u} [Pixel px] [PngPixel px]
    (bytes : ByteArray) : Option (PngDecodeResult px) := do
  let parsed ←
    if hsize : 8 <= bytes.size then
      parsePngWithMetadata bytes hsize
    else
      none
  decodeParsedBitmapWithMetadata (px := px) parsed

-- PNG decoder for RGB/RGBA; converts as needed (drops or fills alpha).
def decodeBitmap {px : Type u} [Pixel px] [PngPixel px]
    (bytes : ByteArray) : Option (Bitmap px) := do
  let parsed ←
    if hsize : 8 <= bytes.size then
      parsePngForDecode bytes hsize
    else
      none
  if parsed.metadata.transparency.isSome then
    none
  let parsed :=
    { parsed with metadata := PngMetadata.pixelOnlyColorSpace parsed.metadata }
  let hdr := parsed.header
  let idat := parsed.idat
  if !pngColorTypeBitDepthSupported hdr.colorType hdr.bitDepth then
    none
  if hdr.colorType != 0 && hdr.colorType != 2 && hdr.colorType != 4 &&
      hdr.colorType != 6 then
    none
  let targetBitDepth := PngPixel.bitDepth (α := px)
  let source1 := hdr.bitDepth == 1
  let source16 := hdr.bitDepth == 16
  let target8 := targetBitDepth == u8 8
  let target16 := targetBitDepth == u8 16
  let bitDepthCompatible :=
    hdr.bitDepth == targetBitDepth.toNat ||
      (source16 && target8) ||
      (source1 && (target8 || target16))
  if !bitDepthCompatible then
    none
  if hdr.colorType == 4 &&
      PngPixel.colorType (α := px) != u8 4 && PngPixel.colorType (α := px) != u8 6 then
    none
  let inflated ←
    if hsize : 2 <= idat.size then
      match zlibDecompressStored idat hsize with
      | some raw => some raw
      | none => zlibDecompress idat hsize
    else
      none
  let (raw, bpp, rowBytes) ←
    if source1 then
      let packedRowBytes := gray1RowBytes hdr.width
      let packedRaw ← normalizeGray1RawByInterlace? inflated hdr
      let expected := hdr.height * (packedRowBytes + 1)
      if packedRaw.size != expected then
        none
      let flat ← decodeRowsLoopGray1Packed packedRaw hdr.width hdr.height
      let virtualBitDepth := if target16 then 16 else 8
      let raw := gray1FlatToSampleRaw flat hdr.width hdr.height virtualBitDepth
      let bpp := if target16 then 2 else 1
      let rowBytes := hdr.width * bpp
      some (raw, bpp, rowBytes)
    else
      let bpp ← pngBytesPerPixelForColorTypeAndBitDepth? hdr.colorType hdr.bitDepth
      let rowBytes := hdr.width * bpp
      let raw ← normalizeRawByInterlace? inflated hdr bpp
      let expected := hdr.height * (rowBytes + 1)
      if raw.size != expected then
        none
      some (raw, bpp, rowBytes)
  let totalBytes := hdr.width * hdr.height * Pixel.bytesPerPixel (α := px)
  let pixels0 := ByteArray.mk <| Array.replicate totalBytes 0
  let targetColorType := PngPixel.colorType (α := px)
  let chrmGrayActive :=
    parsed.metadata.srgb.isNone && parsed.metadata.chromaticities.isSome &&
    (hdr.colorType == 2 || hdr.colorType == 6) &&
    (targetColorType == u8 0 || targetColorType == u8 4)
  let pixels ←
    if chrmGrayActive then
      match parsed.metadata.chromaticities with
      | some chromaticities =>
          match chromaticities.sourceToSrgbMatrix? with
          | some matrix =>
              decodeRowsLoopChrmToGrayTarget matrix parsed.metadata.gamma targetColorType
                hdr.colorType source16 target8 target16 raw hdr.width hdr.height bpp rowBytes pixels0
          | none => none
      | none => none
    else if source16 && target8 then
      decodeRowsLoopDown16To8 targetColorType hdr.colorType
        raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
    else
      PngPixel.decodeRowsLoop (α := px) raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
  let pixels ← applyPngColorSpaceTransform parsed.metadata hdr.colorType
    targetColorType targetBitDepth pixels
  let size : Size := { width := hdr.width, height := hdr.height }
  if hsize : pixels.size = size.width * size.height * Pixel.bytesPerPixel (α := px) then
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

def encodeRawPrefix (data : ByteArray) (rowBytes : Nat) : Nat → ByteArray → ByteArray
  | 0, raw => raw
  | y + 1, raw =>
      let raw' := encodeRawPrefix data rowBytes y raw
      let outOff := y * (rowBytes + 1)
      let start := y * rowBytes
      data.copySlice start raw' (outOff + 1) rowBytes

def encodeRaw {px : Type u} [Pixel px] (bmp : Bitmap px) : ByteArray :=
  let w := bmp.size.width
  let h := bmp.size.height
  let rowBytes := w * Pixel.bytesPerPixel (α := px)
  let rawSize := h * (rowBytes + 1)
  let raw := ByteArray.mk <| Array.replicate rawSize 0
  encodeRawLoop bmp.data rowBytes h 0 raw

def encodeRawFast {px : Type u} [Pixel px] (bmp : Bitmap px) : ByteArray :=
  let w := bmp.size.width
  let h := bmp.size.height
  let rowBytes := w * Pixel.bytesPerPixel (α := px)
  let rawSize := h * (rowBytes + 1)
  let raw := ByteArray.mk <| Array.replicate rawSize 0
  encodeRawPrefix bmp.data rowBytes h raw

def encodeRawFilteredRows (data : ByteArray) (rowBytes h y : Nat)
    (prev raw : ByteArray) (strategy : PngFilterStrategy) (bpp : Nat) : ByteArray :=
  if hlt : y < h then
    let start := y * rowBytes
    let row := data.extract start (start + rowBytes)
    let filtered := filterRowForStrategy strategy row prev bpp
    let raw := raw.push filtered.1
    let raw := raw ++ filtered.2
    encodeRawFilteredRows data rowBytes h (y + 1) row raw strategy bpp
  else
    raw
termination_by h - y
decreasing_by
  have hy : y < h := hlt
  have hy' : y < y + 1 := Nat.lt_succ_self y
  exact Nat.sub_lt_sub_left hy hy'

def encodeRawWithFilter {px : Type u} [Pixel px] (bmp : Bitmap px)
    (strategy : PngFilterStrategy) : ByteArray :=
  match strategy with
  | .none => encodeRawFast bmp
  | _ =>
      let w := bmp.size.width
      let h := bmp.size.height
      let bpp := Pixel.bytesPerPixel (α := px)
      let rowBytes := w * bpp
      let rawSize := h * (rowBytes + 1)
      let raw := ByteArray.emptyWithCapacity rawSize
      encodeRawFilteredRows bmp.data rowBytes h 0 ByteArray.empty raw strategy bpp

def encodeRawGray1 (bmp : BitmapGray1) : ByteArray :=
  let rowBytes := gray1RowBytes bmp.size.width
  let rawSize := bmp.size.height * (rowBytes + 1)
  let raw := ByteArray.mk <| Array.replicate rawSize 0
  encodeRawPrefix bmp.data rowBytes bmp.size.height raw

def encodeRawGray1WithFilter (bmp : BitmapGray1) (strategy : PngFilterStrategy) : ByteArray :=
  match strategy with
  | .none => encodeRawGray1 bmp
  | _ =>
      let rowBytes := gray1RowBytes bmp.size.width
      let rawSize := bmp.size.height * (rowBytes + 1)
      let raw := ByteArray.emptyWithCapacity rawSize
      encodeRawFilteredRows bmp.data rowBytes bmp.size.height 0 ByteArray.empty raw strategy 1

def encodeI32BE? (n : Int) : Option ByteArray := do
  let encoded ← signed32ToU32? n
  some (u32be encoded)

def encodeChrmData? (chromaticities : PngChromaticities) : Option ByteArray := do
  if !chromaticities.valid then
    none
  let wx ← encodeI32BE? chromaticities.white.x
  let wy ← encodeI32BE? chromaticities.white.y
  let rx ← encodeI32BE? chromaticities.red.x
  let ry ← encodeI32BE? chromaticities.red.y
  let gx ← encodeI32BE? chromaticities.green.x
  let gy ← encodeI32BE? chromaticities.green.y
  let bx ← encodeI32BE? chromaticities.blue.x
  let byBytes ← encodeI32BE? chromaticities.blue.y
  some (wx ++ wy ++ rx ++ ry ++ gx ++ gy ++ bx ++ byBytes)

def encodeChrmChunk? (chromaticities : Option PngChromaticities) : Option ByteArray := do
  match chromaticities with
  | none => some ByteArray.empty
  | some chromaticities =>
      let data ← encodeChrmData? chromaticities
      some (mkChunkBytes chrmTypeBytes data)

def encodeColorSpaceChunks? (colorSpace : Option PngEncodeColorSpace)
    (chromaticities : Option PngChromaticities) : Option ByteArray := do
  let chrmChunk ← encodeChrmChunk? chromaticities
  match colorSpace with
  | none => some chrmChunk
  | some (.gamma gammaScaled) =>
      if gammaScaled == 0 then
        none
      else
        some (mkChunkBytes gamaTypeBytes (u32be gammaScaled) ++ chrmChunk)
  | some (.srgb intent includeCompatGamma) =>
      match chromaticities with
      | some chromaticities =>
          if chromaticities ≠ PngChromaticities.srgb then
            none
      | none =>
          pure ()
      let srgbChunk := mkChunkBytes srgbTypeBytes (ByteArray.mk #[intent.toByte])
      let prefixBytes :=
        if includeCompatGamma then
          mkChunkBytes gamaTypeBytes (u32be 45455)
        else
          ByteArray.empty
      some (prefixBytes ++ chrmChunk ++ srgbChunk)

def encodeTimeChunk? (modificationTime : Option PngTime) : Option ByteArray := do
  match modificationTime with
  | none => some ByteArray.empty
  | some time =>
      let data ← encodeTimeData? time
      some (mkChunkBytes timeTypeBytes data)

def encodePhysData? (physical : PngPhysicalPixelDimensions) : Option ByteArray :=
  if physical.valid then
    some <| u32be physical.xPixelsPerUnit ++ u32be physical.yPixelsPerUnit ++
      ByteArray.mk #[physical.unit.toByte]
  else
    none

def encodePhysChunk? (physical : Option PngPhysicalPixelDimensions) : Option ByteArray := do
  match physical with
  | none => some ByteArray.empty
  | some physical =>
      let data ← encodePhysData? physical
      some (mkChunkBytes physTypeBytes data)

def encodeAncillaryChunks? (colorSpace : Option PngEncodeColorSpace)
    (chromaticities : Option PngChromaticities)
    (physical : Option PngPhysicalPixelDimensions)
    (modificationTime : Option PngTime) : Option ByteArray := do
  let colorSpaceChunks ← encodeColorSpaceChunks? colorSpace chromaticities
  let physChunk ← encodePhysChunk? physical
  let timeChunk ← encodeTimeChunk? modificationTime
  some (colorSpaceChunks ++ physChunk ++ timeChunk)

def encodeBitmapCore (raw ihdr : ByteArray) (mode : PngEncodeMode)
    (colorSpace : Option PngEncodeColorSpace) (chromaticities : Option PngChromaticities)
    (physical : Option PngPhysicalPixelDimensions)
    (modificationTime : Option PngTime) : Option ByteArray := do
  let ancillary ← encodeAncillaryChunks? colorSpace chromaticities physical modificationTime
  let idat :=
    match mode with
    | .stored => zlibCompressStored raw
    | .fixed => zlibCompressFixed raw
    | .dynamic => zlibCompressDynamic raw
  let ihdrChunk := mkChunkBytes ihdrTypeBytes ihdr
  let idatChunk := mkChunkBytes idatTypeBytes idat
  let iendChunk := mkChunkBytes iendTypeBytes ByteArray.empty
  let outSize := pngSignature.size + ihdrChunk.size + ancillary.size + idatChunk.size + iendChunk.size
  let out := ByteArray.emptyWithCapacity outSize
  some (out ++ pngSignature ++ ihdrChunk ++ ancillary ++ idatChunk ++ iendChunk)

def decodeParsedBitmapGray1WithMetadata (parsed : PngParsed) :
    Option PngDecodeGray1Result := do
  let hdr := parsed.header
  if hdr.colorType != 0 || hdr.bitDepth != 1 then
    none
  let packedRowBytes := gray1RowBytes hdr.width
  let inflated ←
    if hsize : 2 <= parsed.idat.size then
      match zlibDecompressStored parsed.idat hsize with
      | some raw => some raw
      | none => zlibDecompress parsed.idat hsize
    else
      none
  let packedRaw ← normalizeGray1RawByInterlace? inflated hdr
  let expected := hdr.height * (packedRowBytes + 1)
  if packedRaw.size != expected then
    none
  let pixels ← decodeRowsLoopGray1Packed packedRaw hdr.width hdr.height
  let size : Size := { width := hdr.width, height := hdr.height }
  if hvalid : pixels.size = gray1DataSize size.width size.height then
    some
      { bitmap := { size, data := pixels, valid := hvalid }
        metadata := parsed.metadata }
  else
    none

def decodeBitmapGray1WithMetadata (bytes : ByteArray) :
    Option PngDecodeGray1Result := do
  let parsed ←
    if hsize : 8 <= bytes.size then
      parsePngWithMetadata bytes hsize
    else
      none
  decodeParsedBitmapGray1WithMetadata parsed

def decodeBitmapGray1 (bytes : ByteArray) : Option BitmapGray1 := do
  let parsed ←
    if hsize : 8 <= bytes.size then
      parsePngForDecode bytes hsize
    else
      none
  if parsed.metadata.transparency.isSome then
    none
  decodeParsedBitmapGray1WithMetadata
    { parsed with metadata := PngMetadata.pixelOnlyColorSpace parsed.metadata }
    |>.map (fun decoded => decoded.bitmap)

def encodeBitmapGray1 (bmp : BitmapGray1)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode := .fixed) : ByteArray :=
  have _ := hw
  have _ := hh
  Id.run do
    let w := bmp.size.width
    let h := bmp.size.height
    let raw := encodeRawGray1 bmp
    let ihdr := u32be w ++ u32be h ++
      ByteArray.mk #[u8 1, u8 0, u8 0, u8 0, u8 0]
    let idat :=
      match mode with
      | .stored => zlibCompressStored raw
      | .fixed => zlibCompressFixed raw
      | .dynamic => zlibCompressDynamic raw
    let ihdrChunk := mkChunkBytes ihdrTypeBytes ihdr
    let idatChunk := mkChunkBytes idatTypeBytes idat
    let iendChunk := mkChunkBytes iendTypeBytes ByteArray.empty
    let outSize := pngSignature.size + ihdrChunk.size + idatChunk.size + iendChunk.size
    let out := ByteArray.emptyWithCapacity outSize
    out ++ pngSignature ++ ihdrChunk ++ idatChunk ++ iendChunk

def encodeBitmapGray1WithOptions (bmp : BitmapGray1)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (options : PngEncodeOptions := {}) : Option ByteArray :=
  have _ := hw
  have _ := hh
  let raw := encodeRawGray1WithFilter bmp options.filter
  let ihdr := u32be bmp.size.width ++ u32be bmp.size.height ++
    ByteArray.mk #[u8 1, u8 0, u8 0, u8 0, u8 0]
  encodeBitmapCore raw ihdr options.mode options.colorSpace options.chromaticities
    options.physical options.modificationTime

def encodeBitmapGray1Checked (bmp : BitmapGray1)
    (mode : PngEncodeMode := .fixed) : Except String ByteArray :=
  if hw : bmp.size.width < UInt32.size then
    if hh : bmp.size.height < UInt32.size then
      Except.ok (encodeBitmapGray1 bmp hw hh mode)
    else
      Except.error "bitmap height exceeds PNG limit (2^32)"
  else
    Except.error "bitmap width exceeds PNG limit (2^32)"

def encodeBitmapGray1WithOptionsChecked (bmp : BitmapGray1)
    (options : PngEncodeOptions := {}) : Except String ByteArray :=
  if hw : bmp.size.width < UInt32.size then
    if hh : bmp.size.height < UInt32.size then
      match encodeBitmapGray1WithOptions bmp hw hh options with
      | some bytes => Except.ok bytes
      | none => Except.error "invalid PNG ancillary encode options"
    else
      Except.error "bitmap height exceeds PNG limit (2^32)"
  else
    Except.error "bitmap width exceeds PNG limit (2^32)"

def encodeBitmap {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (mode : PngEncodeMode := .fixed) : ByteArray :=
  have _ := hw
  have _ := hh
  Id.run do
    let w := bmp.size.width
    let h := bmp.size.height
    let raw := PngPixel.encodeRaw (α := px) bmp
    let ihdr := u32be w ++ u32be h ++
      ByteArray.mk #[PngPixel.bitDepth (α := px), PngPixel.colorType (α := px), u8 0, u8 0, u8 0]
    let idat :=
      match mode with
      | .stored => zlibCompressStored raw
      | .fixed => zlibCompressFixed raw
      | .dynamic => zlibCompressDynamic raw
    let ihdrChunk := mkChunkBytes ihdrTypeBytes ihdr
    let idatChunk := mkChunkBytes idatTypeBytes idat
    let iendChunk := mkChunkBytes iendTypeBytes ByteArray.empty
    let outSize := pngSignature.size + ihdrChunk.size + idatChunk.size + iendChunk.size
    let out := ByteArray.emptyWithCapacity outSize
    out ++ pngSignature ++ ihdrChunk ++ idatChunk ++ iendChunk

def encodeBitmapWithOptions {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size)
    (options : PngEncodeOptions := {}) : Option ByteArray :=
  have _ := hw
  have _ := hh
  let raw :=
    match options.filter with
    | .none => PngPixel.encodeRaw (α := px) bmp
    | _ => encodeRawWithFilter bmp options.filter
  let ihdr := u32be bmp.size.width ++ u32be bmp.size.height ++
    ByteArray.mk #[PngPixel.bitDepth (α := px), PngPixel.colorType (α := px), u8 0, u8 0, u8 0]
  encodeBitmapCore raw ihdr options.mode options.colorSpace options.chromaticities
    options.physical options.modificationTime

-- Encode a bitmap using the buffered fixed-Huffman deflate blocks (perf testing).

-- Encode a bitmap using fixed-Huffman deflate blocks.
def encodeBitmapFixed {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < UInt32.size) (hh : bmp.size.height < UInt32.size) : ByteArray :=
  encodeBitmap bmp hw hh .fixed

-- Encode a bitmap, returning an error if dimensions exceed PNG limits.
def encodeBitmapChecked {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (mode : PngEncodeMode := .fixed) : Except String ByteArray :=
  if hw : bmp.size.width < UInt32.size then
    if hh : bmp.size.height < UInt32.size then
      Except.ok (encodeBitmap bmp hw hh mode)
    else
      Except.error "bitmap height exceeds PNG limit (2^32)"
  else
    Except.error "bitmap width exceeds PNG limit (2^32)"

def encodeBitmapWithOptionsChecked {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (options : PngEncodeOptions := {}) : Except String ByteArray :=
  if hw : bmp.size.width < UInt32.size then
    if hh : bmp.size.height < UInt32.size then
      match encodeBitmapWithOptions bmp hw hh options with
      | some bytes => Except.ok bytes
      | none => Except.error "invalid PNG ancillary encode options"
    else
      Except.error "bitmap height exceeds PNG limit (2^32)"
  else
    Except.error "bitmap width exceeds PNG limit (2^32)"

def PngTime.ofDateTimeUTC? (dt : Std.Time.DateTime Std.Time.TimeZone.UTC) : Option PngTime :=
  let year := (dt.year : Int)
  if year < 0 then
    none
  else
    let time : PngTime :=
      { year := year.toNat
        month := dt.month.val.toNat
        day := dt.day.val.toNat
        hour := dt.hour.val.toNat
        minute := dt.minute.val.toNat
        second := dt.second.val.toNat }
    if time.valid then some time else none

def currentPngTimeUTC? : IO (Except String PngTime) := do
  let dt ← Std.Time.DateTime.now (tz := Std.Time.TimeZone.UTC)
  match PngTime.ofDateTimeUTC? dt with
  | some time => pure (Except.ok time)
  | none => pure (Except.error "current UTC time is outside PNG tIME range")

def PngEncodeOptions.withCurrentModificationTime
    (options : PngEncodeOptions) : IO (Except String PngEncodeOptions) := do
  if options.modificationTime.isSome then
    pure (Except.ok options)
  else
    match ← currentPngTimeUTC? with
    | Except.ok time => pure (Except.ok { options with modificationTime := some time })
    | Except.error err => pure (Except.error err)

def Bitmap.readPng {px : Type u} [Pixel px] [PngPixel px]
    (path : FilePath) : IO (Except String (Bitmap px)) := do
  let bytesOrErr <- ioToExcept (IO.FS.readBinFile path)
  match bytesOrErr with
  | Except.error err => pure (Except.error err)
  | Except.ok bytes =>
      match decodeBitmap (px := px) bytes with
      | some bmp => pure (Except.ok bmp)
      | none => pure (Except.error "invalid PNG bitmap")

def BitmapGray1.readPng (path : FilePath) : IO (Except String BitmapGray1) := do
  let bytesOrErr <- ioToExcept (IO.FS.readBinFile path)
  match bytesOrErr with
  | Except.error err => pure (Except.error err)
  | Except.ok bytes =>
      match decodeBitmapGray1 bytes with
      | some bmp => pure (Except.ok bmp)
      | none => pure (Except.error "invalid PNG bitmap")

def BitmapGray1.writePng (path : FilePath) (bmp : BitmapGray1)
    (mode : PngEncodeMode := .fixed) : IO (Except String Unit) := do
  match ← ({ mode := mode } : PngEncodeOptions).withCurrentModificationTime with
  | Except.error err => pure (Except.error err)
  | Except.ok options =>
      match encodeBitmapGray1WithOptionsChecked bmp options with
      | Except.error err => pure (Except.error err)
      | Except.ok bytes => ioToExcept (IO.FS.writeBinFile path bytes)

def BitmapGray1.writePngWithOptions (path : FilePath) (bmp : BitmapGray1)
    (options : PngEncodeOptions := {}) : IO (Except String Unit) := do
  match ← options.withCurrentModificationTime with
  | Except.error err => pure (Except.error err)
  | Except.ok options =>
      match encodeBitmapGray1WithOptionsChecked bmp options with
      | Except.error err => pure (Except.error err)
      | Except.ok bytes => ioToExcept (IO.FS.writeBinFile path bytes)

def BitmapGray1.writePngWithoutTime (path : FilePath) (bmp : BitmapGray1)
    (mode : PngEncodeMode := .fixed) : IO (Except String Unit) :=
  match encodeBitmapGray1Checked bmp mode with
  | Except.error err => pure (Except.error err)
  | Except.ok bytes => ioToExcept (IO.FS.writeBinFile path bytes)

def Bitmap.writePngWithOptions {px : Type u} [Pixel px] [PngPixel px]
    (path : FilePath) (bmp : Bitmap px) (options : PngEncodeOptions := {}) :
    IO (Except String Unit) := do
  match ← options.withCurrentModificationTime with
  | Except.error err => pure (Except.error err)
  | Except.ok options =>
      match encodeBitmapWithOptionsChecked (px := px) bmp options with
      | Except.error err => pure (Except.error err)
      | Except.ok bytes => ioToExcept (IO.FS.writeBinFile path bytes)

def Bitmap.writePngWithoutTime {px : Type u} [Pixel px] [PngPixel px]
    (path : FilePath) (bmp : Bitmap px) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  match encodeBitmapChecked (px := px) bmp mode with
  | Except.error err => pure (Except.error err)
  | Except.ok bytes => ioToExcept (IO.FS.writeBinFile path bytes)

def BitmapRGB8.readPng [Pixel PixelRGB8] [PngPixel PixelRGB8]
    (path : FilePath) : IO (Except String BitmapRGB8) :=
  Bitmap.readPng (px := PixelRGB8) path

def BitmapRGB8.writePng [Pixel PixelRGB8] [PngPixel PixelRGB8]
    (path : FilePath) (bmp : BitmapRGB8) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  Bitmap.writePngWithOptions (px := PixelRGB8) path bmp { mode := mode }

def BitmapRGB16.readPng [Pixel PixelRGB16] [PngPixel PixelRGB16]
    (path : FilePath) : IO (Except String BitmapRGB16) :=
  Bitmap.readPng (px := PixelRGB16) path

def BitmapRGB16.writePng [Pixel PixelRGB16] [PngPixel PixelRGB16]
    (path : FilePath) (bmp : BitmapRGB16) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  Bitmap.writePngWithOptions (px := PixelRGB16) path bmp { mode := mode }

def BitmapRGBA8.readPng [Pixel PixelRGBA8] [PngPixel PixelRGBA8]
    (path : FilePath) : IO (Except String BitmapRGBA8) :=
  Bitmap.readPng (px := PixelRGBA8) path

def BitmapRGBA8.writePng [Pixel PixelRGBA8] [PngPixel PixelRGBA8]
    (path : FilePath) (bmp : BitmapRGBA8) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  Bitmap.writePngWithOptions (px := PixelRGBA8) path bmp { mode := mode }

def BitmapRGBA16.readPng [Pixel PixelRGBA16] [PngPixel PixelRGBA16]
    (path : FilePath) : IO (Except String BitmapRGBA16) :=
  Bitmap.readPng (px := PixelRGBA16) path

def BitmapRGBA16.writePng [Pixel PixelRGBA16] [PngPixel PixelRGBA16]
    (path : FilePath) (bmp : BitmapRGBA16) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  Bitmap.writePngWithOptions (px := PixelRGBA16) path bmp { mode := mode }

def BitmapGray8.readPng [Pixel PixelGray8] [PngPixel PixelGray8]
    (path : FilePath) : IO (Except String BitmapGray8) :=
  Bitmap.readPng (px := PixelGray8) path

def BitmapGray8.writePng [Pixel PixelGray8] [PngPixel PixelGray8]
    (path : FilePath) (bmp : BitmapGray8) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  Bitmap.writePngWithOptions (px := PixelGray8) path bmp { mode := mode }

def BitmapGray16.readPng [Pixel PixelGray16] [PngPixel PixelGray16]
    (path : FilePath) : IO (Except String BitmapGray16) :=
  Bitmap.readPng (px := PixelGray16) path

def BitmapGray16.writePng [Pixel PixelGray16] [PngPixel PixelGray16]
    (path : FilePath) (bmp : BitmapGray16) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  Bitmap.writePngWithOptions (px := PixelGray16) path bmp { mode := mode }

def BitmapGrayAlpha8.readPng [Pixel PixelGrayAlpha8] [PngPixel PixelGrayAlpha8]
    (path : FilePath) : IO (Except String BitmapGrayAlpha8) :=
  Bitmap.readPng (px := PixelGrayAlpha8) path

def BitmapGrayAlpha8.writePng [Pixel PixelGrayAlpha8] [PngPixel PixelGrayAlpha8]
    (path : FilePath) (bmp : BitmapGrayAlpha8) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  Bitmap.writePngWithOptions (px := PixelGrayAlpha8) path bmp { mode := mode }

def BitmapGrayAlpha16.readPng [Pixel PixelGrayAlpha16] [PngPixel PixelGrayAlpha16]
    (path : FilePath) : IO (Except String BitmapGrayAlpha16) :=
  Bitmap.readPng (px := PixelGrayAlpha16) path

def BitmapGrayAlpha16.writePng [Pixel PixelGrayAlpha16] [PngPixel PixelGrayAlpha16]
    (path : FilePath) (bmp : BitmapGrayAlpha16) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  Bitmap.writePngWithOptions (px := PixelGrayAlpha16) path bmp { mode := mode }

instance : PngPixel PixelRGB8 where
  encodeRaw := encodeRawFast
  colorType := u8 2
  bitDepth := u8 8
  decodeRowsLoop := decodeRowsLoop

instance : PngPixel PixelRGB16 where
  encodeRaw := encodeRawFast
  colorType := u8 2
  bitDepth := u8 16
  decodeRowsLoop := decodeRowsLoopRGB16

instance : PngPixel PixelRGBA8 where
  encodeRaw := encodeRawFast
  colorType := u8 6
  bitDepth := u8 8
  decodeRowsLoop := decodeRowsLoopRGBA

instance : PngPixel PixelRGBA16 where
  encodeRaw := encodeRawFast
  colorType := u8 6
  bitDepth := u8 16
  decodeRowsLoop := decodeRowsLoopRGBA16

instance : PngPixel PixelGray8 where
  encodeRaw := encodeRawFast
  colorType := u8 0
  bitDepth := u8 8
  decodeRowsLoop := decodeRowsLoopGray

instance : PngPixel PixelGray16 where
  encodeRaw := encodeRawFast
  colorType := u8 0
  bitDepth := u8 16
  decodeRowsLoop := decodeRowsLoopGray16

instance : PngPixel PixelGrayAlpha8 where
  encodeRaw := encodeRawFast
  colorType := u8 4
  bitDepth := u8 8
  decodeRowsLoop := decodeRowsLoopGrayAlpha

instance : PngPixel PixelGrayAlpha16 where
  encodeRaw := encodeRawFast
  colorType := u8 4
  bitDepth := u8 16
  decodeRowsLoop := decodeRowsLoopGrayAlpha16

end Png

instance : FileWritable BitmapGray1 where
  write := fun path bmp => Png.BitmapGray1.writePng path bmp .fixed

instance : FileReadable BitmapGray1 where
  read := Png.BitmapGray1.readPng

instance [Pixel PixelRGB8] [Png.PngPixel PixelRGB8] : FileWritable BitmapRGB8 where
  write := fun path bmp => Png.BitmapRGB8.writePng path bmp .fixed

instance [Pixel PixelRGB8] [Png.PngPixel PixelRGB8] : FileReadable BitmapRGB8 where
  read := Png.BitmapRGB8.readPng

instance [Pixel PixelRGB16] [Png.PngPixel PixelRGB16] : FileWritable BitmapRGB16 where
  write := fun path bmp => Png.BitmapRGB16.writePng path bmp .fixed

instance [Pixel PixelRGB16] [Png.PngPixel PixelRGB16] : FileReadable BitmapRGB16 where
  read := Png.BitmapRGB16.readPng

instance [Pixel PixelRGBA8] [Png.PngPixel PixelRGBA8] : FileWritable BitmapRGBA8 where
  write := fun path bmp => Png.BitmapRGBA8.writePng path bmp .fixed

instance [Pixel PixelRGBA8] [Png.PngPixel PixelRGBA8] : FileReadable BitmapRGBA8 where
  read := Png.BitmapRGBA8.readPng

instance [Pixel PixelRGBA16] [Png.PngPixel PixelRGBA16] : FileWritable BitmapRGBA16 where
  write := fun path bmp => Png.BitmapRGBA16.writePng path bmp .fixed

instance [Pixel PixelRGBA16] [Png.PngPixel PixelRGBA16] : FileReadable BitmapRGBA16 where
  read := Png.BitmapRGBA16.readPng

instance [Pixel PixelGray8] [Png.PngPixel PixelGray8] : FileWritable BitmapGray8 where
  write := fun path bmp => Png.BitmapGray8.writePng path bmp .fixed

instance [Pixel PixelGray8] [Png.PngPixel PixelGray8] : FileReadable BitmapGray8 where
  read := Png.BitmapGray8.readPng

instance [Pixel PixelGray16] [Png.PngPixel PixelGray16] : FileWritable BitmapGray16 where
  write := fun path bmp => Png.BitmapGray16.writePng path bmp .fixed

instance [Pixel PixelGray16] [Png.PngPixel PixelGray16] : FileReadable BitmapGray16 where
  read := Png.BitmapGray16.readPng

instance [Pixel PixelGrayAlpha8] [Png.PngPixel PixelGrayAlpha8] :
    FileWritable BitmapGrayAlpha8 where
  write := fun path bmp => Png.BitmapGrayAlpha8.writePng path bmp .fixed

instance [Pixel PixelGrayAlpha8] [Png.PngPixel PixelGrayAlpha8] :
    FileReadable BitmapGrayAlpha8 where
  read := Png.BitmapGrayAlpha8.readPng

instance [Pixel PixelGrayAlpha16] [Png.PngPixel PixelGrayAlpha16] :
    FileWritable BitmapGrayAlpha16 where
  write := fun path bmp => Png.BitmapGrayAlpha16.writePng path bmp .fixed

instance [Pixel PixelGrayAlpha16] [Png.PngPixel PixelGrayAlpha16] :
    FileReadable BitmapGrayAlpha16 where
  read := Png.BitmapGrayAlpha16.readPng

end Bitmaps
