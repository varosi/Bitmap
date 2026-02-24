import Bitmap.Basic

open System (FilePath)

universe u

namespace Bitmaps

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

def crc32Update (c : UInt32) (bytes : ByteArray) : UInt32 :=
  Id.run do
    let mut c : UInt32 := c
    for b in bytes do
      let idx : Nat := ((c ^^^ (UInt32.ofNat b.toNat)) &&& (0xFF : UInt32)).toNat
      c := crc32Table[idx]! ^^^ (c >>> 8)
    return c

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

@[implemented_by adler32Fast]
def adler32 (bytes : ByteArray) : UInt32 :=
  Id.run do
    let mod : UInt32 := 65521
    let mut a : UInt32 := 1
    let mut b : UInt32 := 0
    for byte in bytes do
      a := a + UInt32.ofNat byte.toNat
      if a >= mod then
        a := a - mod
      b := b + a
      if b >= mod then
        b := b - mod
      if b >= mod then
        b := b - mod
    return (b <<< 16) + a

def pngSignature : ByteArray :=
  ByteArray.mk #[
    u8 0x89, u8 0x50, u8 0x4E, u8 0x47,
    u8 0x0D, u8 0x0A, u8 0x1A, u8 0x0A
  ]

def ihdrTypeBytes : ByteArray := "IHDR".toUTF8
def idatTypeBytes : ByteArray := "IDAT".toUTF8
def iendTypeBytes : ByteArray := "IEND".toUTF8

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
    ++ u16le len ++ u16le (0xFFFF - len) ++ payload

def deflateStoredFastAux (raw : ByteArray) (out : ByteArray) : ByteArray :=
  if _hzero : raw.size = 0 then
    out ++ storedBlock ByteArray.empty true
  else
    let blockLen := if raw.size > 65535 then 65535 else raw.size
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

def deflateStoredFast (raw : ByteArray) : ByteArray :=
  deflateStoredFastAux raw ByteArray.empty

inductive PngEncodeMode
  | stored
  | fixed
deriving Repr, DecidableEq

structure BitWriter where
  out : ByteArray
  cur : UInt8
  bitPos : Nat
  hbit : bitPos < 8
deriving Repr

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

@[inline] def chooseFixedMatchChunkLen (remaining : Nat) : Nat :=
  if remaining > 258 then
    let r := remaining % 258
    if r == 1 then 256
    else if r == 2 then 257
    else 258
  else
    remaining

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

def deflateFixedFast (raw : ByteArray) : ByteArray :=
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

@[implemented_by deflateFixedFast]
def deflateFixed (raw : ByteArray) : ByteArray :=
  let bw0 := BitWriter.empty
  let bw1 := bw0.writeBits 1 1
  let bw2 := bw1.writeBits 1 2
  let bw3 := deflateFixedAux raw.data 0 bw2
  let (eobCode, eobLen) := fixedLitLenCode 256
  let bw4 := bw3.writeBits (reverseBits eobCode eobLen) eobLen
  bw4.flush


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

structure BitReader where
  data : ByteArray
  bytePos : Nat
  bitPos : Nat
  hpos : bytePos ≤ data.size
  hend : bytePos = data.size → bitPos = 0
  hbit : bitPos < 8
deriving Repr

-- Precomputed `2^n` for `n ≤ 8`.
def lowPowNat (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | 6 => 64
  | 7 => 128
  | 8 => 256
  | _ => 1

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
deriving Repr

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
  let distTable ← mkHuffman distLengths
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
  match decodeFixedLiteralBlock br out with
  | some res => some res
  | none => decodeFixedBlockFuelFast (br.data.size * 8 + 1) br out

def decodeFixedBlockSpec (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) :=
  match decodeFixedLiteralBlock br out with
  | some res => some res
  | none => decodeFixedBlockFuel (br.data.size * 8 + 1) br out

@[implemented_by decodeFixedBlockFast]
def decodeFixedBlock (br : BitReader) (out : ByteArray) :
    Option (BitReader × ByteArray) :=
  decodeFixedBlockSpec br out

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
          if len + nlen != 0xFFFF then
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
          let bitDepth := (tail.get! 0).toNat
          let colorType := (tail.get! 1).toNat
          let comp := (tail.get! 2).toNat
          let filter := (tail.get! 3).toNat
          let interlace := (tail.get! 4).toNat
          if bitDepth != 8 then
            none
          if colorType != 0 && colorType != 2 && colorType != 6 then
            none
          if comp != 0 || filter != 0 || interlace != 0 then
            none
          let hdr : PngHeader := { width := w, height := h, colorType, bitDepth }
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


def parsePngLoopFuel (fuel : Nat) (bytes : ByteArray) (pos : Nat)
    (header : Option PngHeader) (idat : ByteArray) : Option (PngHeader × ByteArray) :=
  match fuel with
  | 0 => none
  | fuel + 1 => do
      if hpos : pos + 8 <= bytes.size then
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
                  let header := some { width := w, height := h, colorType, bitDepth }
                  parsePngLoopFuel fuel bytes posNext header idat
                else
                  none
              else if typBytes == "IDAT".toUTF8 then
                parsePngLoopFuel fuel bytes posNext header (idat ++ chunkData)
              else if typBytes == "IEND".toUTF8 then
                match header with
                | none => none
                | some h => some (h, idat)
              else
                parsePngLoopFuel fuel bytes posNext header idat
          | none =>
              none
        else
          none
      else
        match header with
        | none => none
        | some h => some (h, idat)

def parsePng (bytes : ByteArray) (_hsize : 8 <= bytes.size) :
    Option (PngHeader × ByteArray) := do
  if let some res := parsePngSimple bytes _hsize then
    return res
  if bytes.extract 0 8 != pngSignature then
    none
  parsePngLoopFuel (bytes.size + 1) bytes 8 none ByteArray.empty

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

def decodeRowDropAlpha (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let r := row.get! base
      let g := if bpp == 1 then r else row.get! (base + 1)
      let b := if bpp == 1 then r else row.get! (base + 2)
      let pixBase := (y * w + x) * bytesPerPixelRGB
      pixels := pixels.set! pixBase r
      pixels := pixels.set! (pixBase + 1) g
      pixels := pixels.set! (pixBase + 2) b
    return pixels

def decodeRowAddAlpha (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let r := row.get! base
      let g := if bpp == 1 then r else row.get! (base + 1)
      let b := if bpp == 1 then r else row.get! (base + 2)
      let pixBase := (y * w + x) * bytesPerPixelRGBA
      pixels := pixels.set! pixBase r
      pixels := pixels.set! (pixBase + 1) g
      pixels := pixels.set! (pixBase + 2) b
      pixels := pixels.set! (pixBase + 3) (u8 255)
    return pixels

def decodeRowGray (row : ByteArray) (w y bpp : Nat) (pixels : ByteArray) : ByteArray :=
  Id.run do
    let mut pixels := pixels
    for x in [0:w] do
      let base := x * bpp
      let r := row.get! base
      let g := if bpp == 1 then r else row.get! (base + 1)
      let b := if bpp == 1 then r else row.get! (base + 2)
      let gray := u8 ((r.toNat + g.toNat + b.toNat) / 3)
      let pixBase := (y * w + x) * bytesPerPixelGray
      pixels := pixels.set! pixBase gray
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

def decodeRowsLoop (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGB decodeRowDropAlpha
    y offset prevRow pixels

def decodeRowsLoopRGBA (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelRGBA decodeRowAddAlpha
    y offset prevRow pixels

def decodeRowsLoopGray (raw : ByteArray) (w h bpp rowBytes : Nat)
    (y offset : Nat) (prevRow pixels : ByteArray) : Option ByteArray :=
  decodeRowsLoopCore raw w h bpp rowBytes bytesPerPixelGray decodeRowGray
    y offset prevRow pixels

class PngPixel (α : Type u) [Pixel α] where
  encodeRaw : Bitmap α -> ByteArray
  colorType : UInt8
  decodeRowsLoop : (raw : ByteArray) -> (w h bpp rowBytes : Nat) ->
    (y offset : Nat) -> (prevRow pixels : ByteArray) -> Option ByteArray

-- PNG decoder for RGB/RGBA; converts as needed (drops or fills alpha).
def decodeBitmap {px : Type u} [Pixel px] [PngPixel px]
    (bytes : ByteArray) : Option (Bitmap px) := do
  let (hdr, idat) ←
    if hsize : 8 <= bytes.size then
      parsePng bytes hsize
    else
      none
  if hdr.bitDepth != 8 then
    none
  if hdr.colorType != 0 && hdr.colorType != 2 && hdr.colorType != 6 then
    none
  let bpp := if hdr.colorType == 0 then 1 else if hdr.colorType == 2 then 3 else 4
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
  let totalBytes := hdr.width * hdr.height * Pixel.bytesPerPixel (α := px)
  let pixels0 := ByteArray.mk <| Array.replicate totalBytes 0
  let pixels ←
    PngPixel.decodeRowsLoop (α := px) raw hdr.width hdr.height bpp rowBytes 0 0 ByteArray.empty pixels0
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

def encodeBitmap {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32)
    (mode : PngEncodeMode := .fixed) : ByteArray :=
  have _ := hw
  have _ := hh
  Id.run do
    let w := bmp.size.width
    let h := bmp.size.height
    let raw := PngPixel.encodeRaw (α := px) bmp
    let ihdr := u32be w ++ u32be h ++
      ByteArray.mk #[u8 8, PngPixel.colorType (α := px), u8 0, u8 0, u8 0]
    let idat :=
      match mode with
      | .stored => zlibCompressStored raw
      | .fixed => zlibCompressFixed raw
    let ihdrChunk := mkChunkBytes ihdrTypeBytes ihdr
    let idatChunk := mkChunkBytes idatTypeBytes idat
    let iendChunk := mkChunkBytes iendTypeBytes ByteArray.empty
    let outSize := pngSignature.size + ihdrChunk.size + idatChunk.size + iendChunk.size
    let out := ByteArray.emptyWithCapacity outSize
    out ++ pngSignature ++ ihdrChunk ++ idatChunk ++ iendChunk

-- Encode a bitmap using the buffered fixed-Huffman deflate blocks (perf testing).

-- Encode a bitmap using fixed-Huffman deflate blocks.
def encodeBitmapFixed {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (hw : bmp.size.width < 2 ^ 32) (hh : bmp.size.height < 2 ^ 32) : ByteArray :=
  encodeBitmap bmp hw hh .fixed

-- Encode a bitmap, returning an error if dimensions exceed PNG limits.
def encodeBitmapChecked {px : Type u} [Pixel px] [PngPixel px] (bmp : Bitmap px)
    (mode : PngEncodeMode := .fixed) : Except String ByteArray :=
  if hw : bmp.size.width < 2 ^ 32 then
    if hh : bmp.size.height < 2 ^ 32 then
      Except.ok (encodeBitmap bmp hw hh mode)
    else
      Except.error "bitmap height exceeds PNG limit (2^32)"
  else
    Except.error "bitmap width exceeds PNG limit (2^32)"


def Bitmap.readPng {px : Type u} [Pixel px] [PngPixel px]
    (path : FilePath) : IO (Except String (Bitmap px)) := do
  let bytesOrErr <- ioToExcept (IO.FS.readBinFile path)
  match bytesOrErr with
  | Except.error err => pure (Except.error err)
  | Except.ok bytes =>
      match decodeBitmap (px := px) bytes with
      | some bmp => pure (Except.ok bmp)
      | none => pure (Except.error "invalid PNG bitmap")

def BitmapRGB8.readPng [Pixel PixelRGB8] [PngPixel PixelRGB8]
    (path : FilePath) : IO (Except String BitmapRGB8) :=
  Bitmap.readPng (px := PixelRGB8) path

def BitmapRGB8.writePng [Pixel PixelRGB8] [PngPixel PixelRGB8]
    (path : FilePath) (bmp : BitmapRGB8) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  match encodeBitmapChecked (px := PixelRGB8) bmp mode with
  | Except.error err => pure (Except.error err)
  | Except.ok bytes => ioToExcept (IO.FS.writeBinFile path bytes)

def BitmapRGBA8.readPng [Pixel PixelRGBA8] [PngPixel PixelRGBA8]
    (path : FilePath) : IO (Except String BitmapRGBA8) :=
  Bitmap.readPng (px := PixelRGBA8) path

def BitmapRGBA8.writePng [Pixel PixelRGBA8] [PngPixel PixelRGBA8]
    (path : FilePath) (bmp : BitmapRGBA8) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  match encodeBitmapChecked (px := PixelRGBA8) bmp mode with
  | Except.error err => pure (Except.error err)
  | Except.ok bytes => ioToExcept (IO.FS.writeBinFile path bytes)

def BitmapGray8.readPng [Pixel PixelGray8] [PngPixel PixelGray8]
    (path : FilePath) : IO (Except String BitmapGray8) :=
  Bitmap.readPng (px := PixelGray8) path

def BitmapGray8.writePng [Pixel PixelGray8] [PngPixel PixelGray8]
    (path : FilePath) (bmp : BitmapGray8) (mode : PngEncodeMode := .fixed) :
    IO (Except String Unit) :=
  match encodeBitmapChecked (px := PixelGray8) bmp mode with
  | Except.error err => pure (Except.error err)
  | Except.ok bytes => ioToExcept (IO.FS.writeBinFile path bytes)

end Png

instance [Pixel PixelRGB8] [Png.PngPixel PixelRGB8] : FileWritable BitmapRGB8 where
  write := fun path bmp => Png.BitmapRGB8.writePng path bmp .fixed

instance [Pixel PixelRGB8] [Png.PngPixel PixelRGB8] : FileReadable BitmapRGB8 where
  read := Png.BitmapRGB8.readPng

instance [Pixel PixelRGBA8] [Png.PngPixel PixelRGBA8] : FileWritable BitmapRGBA8 where
  write := fun path bmp => Png.BitmapRGBA8.writePng path bmp .fixed

instance [Pixel PixelRGBA8] [Png.PngPixel PixelRGBA8] : FileReadable BitmapRGBA8 where
  read := Png.BitmapRGBA8.readPng

instance [Pixel PixelGray8] [Png.PngPixel PixelGray8] : FileWritable BitmapGray8 where
  write := fun path bmp => Png.BitmapGray8.writePng path bmp .fixed

instance [Pixel PixelGray8] [Png.PngPixel PixelGray8] : FileReadable BitmapGray8 where
  read := Png.BitmapGray8.readPng

end Bitmaps
