import Bitmap
import Lean

open Lean Widget
open System (FilePath)

namespace Bitmaps
namespace Widget

-- Widget props and helpers

structure BitmapWidgetProps where
  width : Nat
  height : Nat
  bytes : ByteArray
  bytesPerPixel : Nat := bytesPerPixelRGB
  pixelSize : Nat := 10
  showGrid : Bool := true
  background : String := "#070a16"
  caption : Option String := none
  deriving Repr, Inhabited, BEq, DecidableEq, ToJson, FromJson, Server.RpcEncodable

def BitmapRGB8.widgetProps (bmp : BitmapRGB8)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none) :
    BitmapWidgetProps :=
  { width := bmp.size.width
    height := bmp.size.height
    bytes := bmp.data
    bytesPerPixel := bytesPerPixelRGB
    pixelSize := max pixelSize 1
    showGrid
    background
    caption }

def BitmapRGBA8.widgetProps (bmp : BitmapRGBA8)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none) :
    BitmapWidgetProps :=
  { width := bmp.size.width
    height := bmp.size.height
    bytes := bmp.data
    bytesPerPixel := bytesPerPixelRGBA
    pixelSize := max pixelSize 1
    showGrid
    background
    caption }

def BitmapGray8.widgetProps (bmp : BitmapGray8)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none) :
    BitmapWidgetProps :=
  { width := bmp.size.width
    height := bmp.size.height
    bytes := bmp.data
    bytesPerPixel := bytesPerPixelGray
    pixelSize := max pixelSize 1
    showGrid
    background
    caption }

-------------------------------------------------------------------------------
-- Sample bitmap and widget integration

private def clampToByte (n : Nat) : UInt8 :=
  UInt8.ofNat (n % 256)

def auroraBitmap : BitmapRGB8 :=
  let width := 56
  let height := 32
  Bitmap.ofPixelFn width height (fun idx : Fin (width * height) =>
    let x := idx.val % width
    let y := idx.val / width
    let diag := x + y
    let swirl := (x * 11 + (height - y) * 7) % 256
    let r := clampToByte (diag * 4 + y * 2)
    let g := clampToByte (swirl + 40)
    let b := clampToByte ((width - x) * 5 + (height - y) * 3)
    PixelRGB.mk r g b)

def testPngPath : FilePath :=
  FilePath.mk "test.png"

def testPngRgbaPath : FilePath :=
  FilePath.mk "test_rgba.png"

def testPngGrayPath : FilePath :=
  FilePath.mk "test_gray.png"

def testPngBitmapResult : Except String BitmapRGB8 :=
  match unsafe unsafeIO (IO.FS.readBinFile testPngPath) with
  | Except.ok bytes =>
      match Png.decodeBitmap bytes with
      | some bmp => Except.ok bmp
      | none => Except.error "invalid PNG bitmap"
  | Except.error err => Except.error err.toString

def testPngRgbaBitmapResult : Except String BitmapRGBA8 :=
  match unsafe unsafeIO (IO.FS.readBinFile testPngRgbaPath) with
  | Except.ok bytes =>
      match Png.decodeBitmap (px := PixelRGBA8) bytes with
      | some bmp => Except.ok bmp
      | none => Except.error "invalid PNG bitmap"
  | Except.error err => Except.error err.toString

def testPngGrayBitmapResult : Except String BitmapGray8 :=
  match unsafe unsafeIO (IO.FS.readBinFile testPngGrayPath) with
  | Except.ok bytes =>
      match Png.decodeBitmap (px := PixelGray8) bytes with
      | some bmp => Except.ok bmp
      | none => Except.error "invalid PNG bitmap"
  | Except.error err => Except.error err.toString

def testPngWidgetProps : BitmapWidgetProps :=
  match testPngBitmapResult with
  | Except.ok bmp =>
      BitmapRGB8.widgetProps bmp
        (pixelSize := 2)
        (background := "#07101f")
        (caption := some "test.png (256×256) loaded from disk")
  | Except.error err =>
      BitmapRGB8.widgetProps (mkBlankBitmap 1 1 { r := 0, g := 0, b := 0 })
        (pixelSize := 2)
        (background := "#1b0b0b")
        (caption := some s!"PNG load failed: {err}")

def testPngRgbaWidgetProps : BitmapWidgetProps :=
  match testPngRgbaBitmapResult with
  | Except.ok bmp =>
      BitmapRGBA8.widgetProps bmp
        (pixelSize := 18)
        (background := "#0b0b12")
        (caption := some "test_rgba.png (4×4) with alpha")
  | Except.error err =>
      BitmapRGBA8.widgetProps (mkBlankBitmapRGBA 1 1 { r := 0, g := 0, b := 0, a := 0 })
        (pixelSize := 18)
        (background := "#1b0b0b")
        (caption := some s!"PNG RGBA load failed: {err}")

def testPngGrayWidgetProps : BitmapWidgetProps :=
  match testPngGrayBitmapResult with
  | Except.ok bmp =>
      BitmapGray8.widgetProps bmp
        (pixelSize := 18)
        (background := "#0b0b12")
        (caption := some "test_gray.png (8×8) grayscale")
  | Except.error err =>
      BitmapGray8.widgetProps (mkBlankBitmapGray 1 1 { v := 0 })
        (pixelSize := 18)
        (background := "#1b0b0b")
        (caption := some s!"PNG Gray load failed: {err}")

@[widget_module]
def bitmapWidget : Lean.Widget.Module where
  javascript := "
    import * as React from 'react'

    const infoStyle = { color: '#f0f3ff', fontSize: '0.85rem' }
    const captionStyle = { color: '#c8d3ff', fontSize: '0.8rem' }

    function wrapperStyle(background) {
      return {
        background,
        padding: '0.85rem 1.1rem',
        borderRadius: '0.85rem',
        display: 'inline-flex',
        flexDirection: 'column',
        gap: '0.45rem',
        boxShadow: '0 18px 40px rgba(0,0,0,0.35)',
        border: '1px solid rgba(255,255,255,0.08)'
      }
    }

    export default function BitmapWidget(props) {
      const canvasRef = React.useRef(null)
      const width = props.width ?? 0
      const height = props.height ?? 0
      const pixelSize = Math.max(props.pixelSize ?? 10, 1)

      React.useEffect(() => {
        const canvas = canvasRef.current
        if (!canvas) return
        const ctx = canvas.getContext('2d')
        if (!ctx) return
        canvas.width = width
        canvas.height = height
        if (!width || !height) {
          ctx.clearRect(0, 0, canvas.width, canvas.height)
          return
        }
        const bytes = props.bytes ?? []
        const stride = Math.max(props.bytesPerPixel ?? 3, 1)
        const image = ctx.createImageData(width, height)
        for (let i = 0; i < width * height; i++) {
          const offset = i * 4
          const base = i * stride
        const r = bytes[base] ?? 0
        const g = stride === 1 ? r : (bytes[base + 1] ?? 0)
        const b = stride === 1 ? r : (bytes[base + 2] ?? 0)
        const a = stride >= 4 ? (bytes[base + 3] ?? 255) : 255
          image.data[offset + 0] = r
          image.data[offset + 1] = g
          image.data[offset + 2] = b
          image.data[offset + 3] = a
        }
        ctx.putImageData(image, 0, 0)
      }, [width, height, props.bytes])

      const frameStyle = {
        position: 'relative',
        width: width * pixelSize,
        height: height * pixelSize,
        borderRadius: '0.5rem',
        overflow: 'hidden'
      }

      const canvasStyle = {
        width: '100%',
        height: '100%',
        imageRendering: 'pixelated',
        display: 'block'
      }

      const gridOverlay = props.showGrid
        ? React.createElement('div', {
            style: {
              position: 'absolute',
              inset: 0,
              pointerEvents: 'none',
              backgroundImage: `linear-gradient(rgba(255,255,255,0.08) 1px, transparent 1px), linear-gradient(90deg, rgba(255,255,255,0.08) 1px, transparent 1px)`,
              backgroundSize: `${pixelSize}px ${pixelSize}px`
            }
          })
        : null

      const caption = props.caption
        ? React.createElement('div', { style: captionStyle }, props.caption)
        : null

      return React.createElement(
        'div',
        { style: wrapperStyle(props.background ?? '#050914') },
        React.createElement(
          'div',
          { style: frameStyle },
          React.createElement('canvas', { ref: canvasRef, style: canvasStyle }),
          gridOverlay
        ),
        React.createElement('div', { style: infoStyle }, `${width} × ${height} pixels`),
        caption
      )
    }
  "

end Widget
end Bitmaps

-- def List.sum [Add α] [OfNat α 0] : List α → α
-- Fin class for Bitmap?
-- USize (OS bit integer, like C unsigned long)
-- LinearAlgebra namespace - https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/AffineSpace/AffineEquiv.html
-- dbgTraceIfShared

open Bitmaps
open Bitmaps.Widget

#widget bitmapWidget with
  (BitmapRGB8.widgetProps auroraBitmap
    (pixelSize := 18)
    (background := "#040b18")
    (caption := some "Aurora bitmap rendered via Lean"))

#widget bitmapWidget with
  (testPngWidgetProps)

#widget bitmapWidget with
  (testPngRgbaWidgetProps)
