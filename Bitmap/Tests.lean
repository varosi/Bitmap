import Bitmap.Basic

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

private def perfFillRead (w h : Nat) : IO (Nat × Nat) := do
  let t0 <- IO.monoNanosNow
  let mut img := mkBlankBitmap w h { r := 0, g := 0, b := 0 }
  let putPixelChecked (bmp : Bitmap) (x y : Nat) (px : PixelRGB8) : Bitmap :=
    if hx : x < bmp.size.width then
      if hy : y < bmp.size.height then
        putPixel bmp x y px hx hy
      else
        bmp
    else
      bmp
  let getPixelChecked (bmp : Bitmap) (x y : Nat) : PixelRGB8 :=
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

private def dimsForPixels (pixels : Nat) : Nat × Nat :=
  let row := 1024
  let h := min row pixels
  let w := max 1 (pixels / h)
  (w, h)

private def runPerfTest : IO Unit := do
  let targetNs : Nat := 5_000_000_000
  let maxPixels : Nat := 70_000_000
  let warmW := 512
  let warmH := 512
  let (warmNs, _) <- perfFillRead warmW warmH
  let warmPixels := warmW * warmH
  let denom := if warmNs == 0 then 1 else warmNs
  let mut targetPixels := (targetNs * warmPixels) / denom
  if targetPixels < 1 then
    targetPixels := 1
  if targetPixels > maxPixels then
    targetPixels := maxPixels

  let mut attempt := 0
  let mut done := false
  let mut lastNs := 0
  let mut lastChecksum := 0
  let mut lastW := 0
  let mut lastH := 0
  while attempt < 2 && !done do
    let (w, h) := dimsForPixels targetPixels
    let (elapsedNs, checksum) <- perfFillRead w h
    lastNs := elapsedNs
    lastChecksum := checksum
    lastW := w
    lastH := h
    if elapsedNs >= targetNs || targetPixels == maxPixels then
      done := true
    else
      let pixels := w * h
      let scaledPixels := (targetNs * pixels) / (if elapsedNs == 0 then 1 else elapsedNs)
      let grown := pixels * 2
      targetPixels := min maxPixels (max grown scaledPixels)
      attempt := attempt + 1

  let elapsedMs := lastNs / 1_000_000
  IO.println s!"perf put/get: {lastW}x{lastH} pixels, {elapsedMs} ms, checksum {lastChecksum}"
  if lastNs < targetNs then
    IO.println s!"perf warning: below 5s target (actual {elapsedMs} ms)"

def run : IO Unit := do
  let ok <- pngRoundTripProperty 20
  if ok then
    IO.println "png round-trip property: ok"
  else
    throw (IO.userError "png round-trip property failed")
  runPerfTest

end Bitmap.Tests

def main : IO Unit :=
  Bitmap.Tests.run
