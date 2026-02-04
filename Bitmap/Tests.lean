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

def run : IO Unit := do
  let ok <- pngRoundTripProperty 20
  if ok then
    IO.println "png round-trip property: ok"
  else
    throw (IO.userError "png round-trip property failed")

end Bitmap.Tests

def main : IO Unit :=
  Bitmap.Tests.run
