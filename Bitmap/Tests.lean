import Bitmap

open Bitmaps

namespace Bitmap.Tests

private def prngStep (s : Nat) : Nat :=
  (1103515245 * s + 12345) % 2147483648

private def randByte (s : Nat) : UInt8 :=
  UInt8.ofNat (s % 256)

private def pixelOfSeed (seed idx : Nat) : PixelRGB8 :=
  let s1 := prngStep (seed + idx)
  let s2 := prngStep (s1 + 1)
  let s3 := prngStep (s2 + 1)
  { r := randByte s1, g := randByte s2, b := randByte s3 }

def bitmapOfSeed (seed w h : Nat) : BitmapRGB8 :=
  Bitmap.ofPixelFn w h (fun i : Fin (w * h) => pixelOfSeed seed i.val)

def pngRoundTripOk (bmp : BitmapRGB8) : Bool :=
  match Png.decodeBitmap (Png.encodeBitmap bmp) with
  | some bmp' => decide (bmp' = bmp)
  | none => false

def pngRoundTripOkRGBA (bmp : BitmapRGBA8) : Bool :=
  match Png.decodeBitmap (px := PixelRGBA8) (Png.encodeBitmap bmp) with
  | some bmp' => decide (bmp' = bmp)
  | none => false

def pngRoundTripProperty (trials : Nat) : IO Bool := do
  let mut ok := true
  let mut i := 0
  while i < trials && ok do
    let w <- IO.rand 1 16
    let h <- IO.rand 1 16
    let seed <- IO.rand 0 1000000
    let bmp := bitmapOfSeed seed w h
    if pngRoundTripOk bmp then
      i := i + 1
    else
      ok := false
  return ok

def pngRoundTripPropertyRGBA (trials : Nat) : IO Bool := do
  let mut ok := true
  let mut i := 0
  while i < trials && ok do
    let w <- IO.rand 1 16
    let h <- IO.rand 1 16
    let seed <- IO.rand 0 1000000
    let bmp := BitmapRGBA8.ofPixelFn w h (fun idx : Fin (w * h) =>
      let px := pixelOfSeed seed idx.val
      let a := randByte (prngStep (seed + idx.val + 7))
      { r := px.r, g := px.g, b := px.b, a := a })
    if pngRoundTripOkRGBA bmp then
      i := i + 1
    else
      ok := false
  return ok

-- Fill a bitmap with deterministic pixels using putPixel, then read all pixels back.
-- Returns elapsed time in nanoseconds and a checksum to prevent dead-code elimination.
private def perfFillRead (w h : Nat) : IO (Nat × Nat) := do
  let t0 <- IO.monoNanosNow
  let mut img := mkBlankBitmap w h { r := 0, g := 0, b := 0 }
  let putPixelChecked (bmp : BitmapRGB8) (x y : Nat) (px : PixelRGB8) : BitmapRGB8 :=
    if hx : x < bmp.size.width then
      if hy : y < bmp.size.height then
        putPixel bmp x y px hx hy
      else
        bmp
    else
      bmp
  let getPixelChecked (bmp : BitmapRGB8) (x y : Nat) : PixelRGB8 :=
    if hx : x < bmp.size.width then
      if hy : y < bmp.size.height then
        getPixel bmp x y hx hy
      else
        { r := 0, g := 0, b := 0 }
    else
      { r := 0, g := 0, b := 0 }
  for y in [0:h] do
    for x in [0:w] do
      let r := UInt8.ofNat ((x + y) % 256)
      let g := UInt8.ofNat ((x * 3 + y) % 256)
      let b := UInt8.ofNat ((x + 2 * y) % 256)
      img := putPixelChecked img x y { r := r, g := g, b := b }
  let mut checksum : Nat := 0
  for y in [0:h] do
    for x in [0:w] do
      let px := getPixelChecked img x y
      checksum := checksum + px.r.toNat + px.g.toNat + px.b.toNat
  let t1 <- IO.monoNanosNow
  return (t1 - t0, checksum)

-- Encode a blank bitmap to PNG and decode it back.
-- Returns elapsed time in nanoseconds and whether the round-trip was exact.
private def perfPngRoundTrip (w h : Nat) : IO (Nat × Bool) := do
  let t0 <- IO.monoNanosNow
  let bmp := mkBlankBitmap w h { r := 0, g := 0, b := 0 }
  let bytes := Png.encodeBitmap bmp
  let ok :=
    match Png.decodeBitmap bytes with
    | some bmp' => decide (bmp' = bmp)
    | none => false
  let t1 <- IO.monoNanosNow
  return (t1 - t0, ok)

-- Fixed-size performance test for putPixel/getPixel on this machine.
-- Chosen so 10 runs total about 5 seconds here.
private def runPerfTest : IO Unit := do
  let w : Nat := 2688
  let h : Nat := 2688
  let iters : Nat := 10
  let mut totalNs : Nat := 0
  let mut totalChecksum : Nat := 0
  for _ in [0:iters] do
    let (elapsedNs, checksum) <- perfFillRead w h
    totalNs := totalNs + elapsedNs
    totalChecksum := totalChecksum + checksum
  let avgNs := totalNs / iters
  let avgMs := avgNs / 1_000_000
  IO.println s!"perf put/get: {w}x{h} pixels, avg {avgMs} ms over {iters} runs, checksum {totalChecksum}"

-- Fixed-size performance test for PNG encode/decode on this machine.
-- Chosen so 10 runs total about 5 seconds here.
private def runPngPerfTest : IO Unit := do
  let w : Nat := 1600
  let h : Nat := 1600
  let iters : Nat := 10
  let mut totalNs : Nat := 0
  for _ in [0:iters] do
    let (elapsedNs, ok) <- perfPngRoundTrip w h
    if !ok then
      throw (IO.userError "png perf round-trip failed")
    totalNs := totalNs + elapsedNs
  let avgNs := totalNs / iters
  let avgMs := avgNs / 1_000_000
  IO.println s!"perf png round-trip: {w}x{h} pixels, avg {avgMs} ms over {iters} runs"

def run : IO Unit := do
  let ok <- pngRoundTripProperty 20
  if ok then
    IO.println "png round-trip property: ok"
  else
    throw (IO.userError "png round-trip property failed")
  let okRgba <- pngRoundTripPropertyRGBA 20
  if okRgba then
    IO.println "png round-trip RGBA property: ok"
  else
    throw (IO.userError "png round-trip RGBA property failed")
  runPerfTest
  runPngPerfTest

end Bitmap.Tests

def main : IO Unit :=
  Bitmap.Tests.run
