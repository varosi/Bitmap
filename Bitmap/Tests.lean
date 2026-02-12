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

private def pixelGrayOfSeed (seed idx : Nat) : PixelGray8 :=
  let s1 := prngStep (seed + idx)
  { v := randByte s1 }

def bitmapOfSeed (seed w h : Nat) : BitmapRGB8 :=
  Bitmap.ofPixelFn w h (fun i : Fin (w * h) => pixelOfSeed seed i.val)

def bitmapGrayOfSeed (seed w h : Nat) : BitmapGray8 :=
  BitmapGray8.ofPixelFn w h (fun i : Fin (w * h) => pixelGrayOfSeed seed i.val)

def pngRoundTripOk (bmp : BitmapRGB8) : Bool :=
  match Png.decodeBitmap (Png.encodeBitmapUnchecked bmp) with
  | some bmp' => decide (bmp' = bmp)
  | none => false

def pngRoundTripOkRGBA (bmp : BitmapRGBA8) : Bool :=
  match Png.decodeBitmap (px := PixelRGBA8) (Png.encodeBitmapUnchecked bmp) with
  | some bmp' => decide (bmp' = bmp)
  | none => false

def pngRoundTripOkGray (bmp : BitmapGray8) : Bool :=
  match Png.decodeBitmap (px := PixelGray8) (Png.encodeBitmapUnchecked bmp) with
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

def pngRoundTripPropertyGray (trials : Nat) : IO Bool := do
  let mut ok := true
  let mut i := 0
  while i < trials && ok do
    let w <- IO.rand 1 16
    let h <- IO.rand 1 16
    let seed <- IO.rand 0 1000000
    let bmp := bitmapGrayOfSeed seed w h
    if pngRoundTripOkGray bmp then
      i := i + 1
    else
      ok := false
  return ok

-- Decode PNG fixtures that use fixed-Huffman deflate blocks.
private def pngDecodeFixedHuffmanFixtures : IO Unit := do
  let grayBytes <- IO.FS.readBinFile "test_gray.png"
  match Png.decodeBitmap (px := PixelGray8) grayBytes with
  | some bmp =>
      if bmp.size.width != 8 || bmp.size.height != 8 then
        throw (IO.userError "fixed-huffman gray fixture has unexpected size")
  | none =>
      throw (IO.userError "fixed-huffman gray fixture failed to decode")
  let rgbaBytes <- IO.FS.readBinFile "test_rgba.png"
  match Png.decodeBitmap (px := PixelRGBA8) rgbaBytes with
  | some bmp =>
      if bmp.size.width != 4 || bmp.size.height != 4 then
        throw (IO.userError "fixed-huffman RGBA fixture has unexpected size")
  | none =>
      throw (IO.userError "fixed-huffman RGBA fixture failed to decode")

-- Fill a bitmap with deterministic pixels using putPixel, then read all pixels back.
-- Returns elapsed time in nanoseconds and a checksum to prevent dead-code elimination.
private def perfFillRead (w h : Nat) : IO (Nat × Nat) := do
  let t0 <- IO.monoNanosNow
  let xs : Array (Fin w) := Array.finRange w
  let ys : Array (Fin h) := Array.finRange h
  let img0 := mkBlankBitmap w h { r := 0, g := 0, b := 0 }
  let acc0 :
      { img : BitmapRGB8 // img.size.width = w ∧ img.size.height = h } :=
    ⟨img0, by rfl, by rfl⟩
  let accFilled :=
    ys.foldl (init := acc0)
      (fun (acc : { img : BitmapRGB8 // img.size.width = w ∧ img.size.height = h }) (y : Fin h) =>
        xs.foldl (init := acc)
          (fun (acc : { img : BitmapRGB8 // img.size.width = w ∧ img.size.height = h }) (x : Fin w) =>
            let img := acc.1
            have hwidth : img.size.width = w := acc.2.1
            have hheight : img.size.height = h := acc.2.2
            have hx : x.val < img.size.width := by
              simp [hwidth]
            have hy : y.val < img.size.height := by
              simp [hheight]
            let r := UInt8.ofNat ((x.val + y.val) % 256)
            let g := UInt8.ofNat ((x.val * 3 + y.val) % 256)
            let b := UInt8.ofNat ((x.val + 2 * y.val) % 256)
            let img' := putPixel img x.val y.val { r := r, g := g, b := b } hx hy
            have hwidth' : img'.size.width = w := by
              have hsame : img'.size.width = img.size.width := by rfl
              exact hsame.trans hwidth
            have hheight' : img'.size.height = h := by
              have hsame : img'.size.height = img.size.height := by rfl
              exact hsame.trans hheight
            ⟨img', hwidth', hheight'⟩))
  let img := accFilled.1
  let hwidth : img.size.width = w := accFilled.2.1
  let hheight : img.size.height = h := accFilled.2.2
  let mut checksum : Nat := 0
  for y in ys do
    for x in xs do
      have hx : x.val < img.size.width := by
        simp [hwidth]
      have hy : y.val < img.size.height := by
        simp [hheight]
      let px := getPixel img x.val y.val hx hy
      checksum := checksum + px.r.toNat + px.g.toNat + px.b.toNat
  let t1 <- IO.monoNanosNow
  return (t1 - t0, checksum)

-- Encode a blank bitmap to PNG and decode it back.
-- Returns elapsed time in nanoseconds and whether the round-trip was exact.
private def perfPngRoundTrip (w h : Nat) : IO (Nat × Bool) := do
  let t0 <- IO.monoNanosNow
  let bmp := mkBlankBitmap w h { r := 0, g := 0, b := 0 }
  let bytes := Png.encodeBitmapUnchecked bmp
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
  let okGray <- pngRoundTripPropertyGray 20
  if okGray then
    IO.println "png round-trip Gray property: ok"
  else
    throw (IO.userError "png round-trip Gray property failed")
  pngDecodeFixedHuffmanFixtures
  runPerfTest
  runPngPerfTest

end Bitmap.Tests

def main : IO Unit :=
  Bitmap.Tests.run
