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
  physicalXPixelsPerUnit : Option Nat := none
  physicalYPixelsPerUnit : Option Nat := none
  physicalUnitIsMeter : Bool := false
  deriving Repr, Inhabited, BEq, DecidableEq, ToJson, FromJson, Server.RpcEncodable

def BitmapWidgetProps.withPhysical (props : BitmapWidgetProps)
    (physical : Option Png.PngPhysicalPixelDimensions) : BitmapWidgetProps :=
  match physical with
  | none => props
  | some physical =>
      { props with
        physicalXPixelsPerUnit := some physical.xPixelsPerUnit,
        physicalYPixelsPerUnit := some physical.yPixelsPerUnit,
        physicalUnitIsMeter := decide (physical.unit = .meter) }

def BitmapWidgetProps.withPngMetadata (props : BitmapWidgetProps)
    (metadata : Png.PngMetadata) : BitmapWidgetProps :=
  props.withPhysical metadata.physical

def BitmapRGB8.widgetProps (bmp : BitmapRGB8)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none)
    (physical : Option Png.PngPhysicalPixelDimensions := none) :
    BitmapWidgetProps :=
  let props : BitmapWidgetProps :=
    { width := bmp.size.width
      height := bmp.size.height
      bytes := bmp.data
      bytesPerPixel := bytesPerPixelRGB
      pixelSize := max pixelSize 1
      showGrid := showGrid
      background := background
      caption := caption }
  props.withPhysical physical

def BitmapRGBA8.widgetProps (bmp : BitmapRGBA8)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none)
    (physical : Option Png.PngPhysicalPixelDimensions := none) :
    BitmapWidgetProps :=
  let props : BitmapWidgetProps :=
    { width := bmp.size.width
      height := bmp.size.height
      bytes := bmp.data
      bytesPerPixel := bytesPerPixelRGBA
      pixelSize := max pixelSize 1
      showGrid := showGrid
      background := background
      caption := caption }
  props.withPhysical physical

def BitmapGray8.widgetProps (bmp : BitmapGray8)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none)
    (physical : Option Png.PngPhysicalPixelDimensions := none) :
    BitmapWidgetProps :=
  let props : BitmapWidgetProps :=
    { width := bmp.size.width
      height := bmp.size.height
      bytes := bmp.data
      bytesPerPixel := bytesPerPixelGray
      pixelSize := max pixelSize 1
      showGrid := showGrid
      background := background
      caption := caption }
  props.withPhysical physical

def BitmapGrayAlpha8.widgetProps (bmp : BitmapGrayAlpha8)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none)
    (physical : Option Png.PngPhysicalPixelDimensions := none) :
    BitmapWidgetProps :=
  let props : BitmapWidgetProps :=
    { width := bmp.size.width
      height := bmp.size.height
      bytes := bmp.data
      bytesPerPixel := bytesPerPixelGrayAlpha
      pixelSize := max pixelSize 1
      showGrid := showGrid
      background := background
      caption := caption }
  props.withPhysical physical

private def expandGray1ToGray8Data (bmp : BitmapGray1) : ByteArray :=
  Id.run do
    let count := bmp.size.width * bmp.size.height
    let mut out := ByteArray.emptyWithCapacity count
    for i in [0:count] do
      out := out.push (if bmp.getBitLinear i then 0xff else 0)
    return out

def BitmapGray1.widgetProps (bmp : BitmapGray1)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none)
    (physical : Option Png.PngPhysicalPixelDimensions := none) :
    BitmapWidgetProps :=
  let props : BitmapWidgetProps :=
    { width := bmp.size.width
      height := bmp.size.height
      bytes := expandGray1ToGray8Data bmp
      bytesPerPixel := bytesPerPixelGray
      pixelSize := max pixelSize 1
      showGrid := showGrid
      background := background
      caption := caption }
  props.withPhysical physical

private def downsampleRGB16ToRGB8Data (data : ByteArray) : ByteArray :=
  Id.run do
    let pixels := data.size / bytesPerPixelRGB16
    let mut out := ByteArray.emptyWithCapacity (pixels * bytesPerPixelRGB)
    for i in [0:pixels] do
      let base := i * bytesPerPixelRGB16
      out := out.push (data.get! base)
      out := out.push (data.get! (base + 2))
      out := out.push (data.get! (base + 4))
    return out

private def downsampleRGBA16ToRGBA8Data (data : ByteArray) : ByteArray :=
  Id.run do
    let pixels := data.size / bytesPerPixelRGBA16
    let mut out := ByteArray.emptyWithCapacity (pixels * bytesPerPixelRGBA)
    for i in [0:pixels] do
      let base := i * bytesPerPixelRGBA16
      out := out.push (data.get! base)
      out := out.push (data.get! (base + 2))
      out := out.push (data.get! (base + 4))
      out := out.push (data.get! (base + 6))
    return out

private def downsampleGray16ToGray8Data (data : ByteArray) : ByteArray :=
  Id.run do
    let pixels := data.size / bytesPerPixelGray16
    let mut out := ByteArray.emptyWithCapacity (pixels * bytesPerPixelGray)
    for i in [0:pixels] do
      let base := i * bytesPerPixelGray16
      out := out.push (data.get! base)
    return out

private def downsampleGrayAlpha16ToGrayAlpha8Data (data : ByteArray) : ByteArray :=
  Id.run do
    let pixels := data.size / bytesPerPixelGrayAlpha16
    let mut out := ByteArray.emptyWithCapacity (pixels * bytesPerPixelGrayAlpha)
    for i in [0:pixels] do
      let base := i * bytesPerPixelGrayAlpha16
      out := out.push (data.get! base)
      out := out.push (data.get! (base + 2))
    return out

def BitmapRGB16.widgetProps (bmp : BitmapRGB16)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none)
    (physical : Option Png.PngPhysicalPixelDimensions := none) :
    BitmapWidgetProps :=
  let props : BitmapWidgetProps :=
    { width := bmp.size.width
      height := bmp.size.height
      bytes := downsampleRGB16ToRGB8Data bmp.data
      bytesPerPixel := bytesPerPixelRGB
      pixelSize := max pixelSize 1
      showGrid := showGrid
      background := background
      caption := caption }
  props.withPhysical physical

def BitmapRGBA16.widgetProps (bmp : BitmapRGBA16)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none)
    (physical : Option Png.PngPhysicalPixelDimensions := none) :
    BitmapWidgetProps :=
  let props : BitmapWidgetProps :=
    { width := bmp.size.width
      height := bmp.size.height
      bytes := downsampleRGBA16ToRGBA8Data bmp.data
      bytesPerPixel := bytesPerPixelRGBA
      pixelSize := max pixelSize 1
      showGrid := showGrid
      background := background
      caption := caption }
  props.withPhysical physical

def BitmapGray16.widgetProps (bmp : BitmapGray16)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none)
    (physical : Option Png.PngPhysicalPixelDimensions := none) :
    BitmapWidgetProps :=
  let props : BitmapWidgetProps :=
    { width := bmp.size.width
      height := bmp.size.height
      bytes := downsampleGray16ToGray8Data bmp.data
      bytesPerPixel := bytesPerPixelGray
      pixelSize := max pixelSize 1
      showGrid := showGrid
      background := background
      caption := caption }
  props.withPhysical physical

def BitmapGrayAlpha16.widgetProps (bmp : BitmapGrayAlpha16)
    (pixelSize : Nat := 12)
    (showGrid : Bool := true)
    (background : String := "#050914")
    (caption : Option String := none)
    (physical : Option Png.PngPhysicalPixelDimensions := none) :
    BitmapWidgetProps :=
  let props : BitmapWidgetProps :=
    { width := bmp.size.width
      height := bmp.size.height
      bytes := downsampleGrayAlpha16ToGrayAlpha8Data bmp.data
      bytesPerPixel := bytesPerPixelGrayAlpha
      pixelSize := max pixelSize 1
      showGrid := showGrid
      background := background
      caption := caption }
  props.withPhysical physical

-------------------------------------------------------------------------------
-- Sample bitmap and widget integration

private def clampToByte (n : Nat) : UInt8 :=
  UInt8.ofNat (n % 256)

private def clampToUInt16 (n : Nat) : UInt16 :=
  UInt16.ofNat (n % 65536)

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

def auroraBitmap16 : BitmapRGB16 :=
  let width := 56
  let height := 32
  BitmapRGB16.ofPixelFn width height (fun idx : Fin (width * height) =>
    let x := idx.val % width
    let y := idx.val / width
    let diag := x + y
    let wave := (x * 2800 + (height - y) * 1700) % 65536
    let r := clampToUInt16 (diag * 1024 + y * 320)
    let g := clampToUInt16 (wave + 8192)
    let b := clampToUInt16 ((width - x) * 1400 + (height - y) * 900)
    PixelRGB.mk r g b)

private def testFixturePath (name : String) : FilePath :=
  FilePath.mk s!"Bitmap/Tests/{name}"

def testPngPath : FilePath :=
  testFixturePath "test.png"

def testPngRgbaPath : FilePath :=
  testFixturePath "test_rgba.png"

def testPngGrayPath : FilePath :=
  testFixturePath "test_gray.png"

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
      const ppuX = props.physicalXPixelsPerUnit ?? null
      const ppuY = props.physicalYPixelsPerUnit ?? null
      const hasPhysical = Number.isFinite(ppuX) && Number.isFinite(ppuY) && ppuX > 0 && ppuY > 0
      const unitIsMeter = props.physicalUnitIsMeter ?? false
      const cssPxPerMeter = 96 / 0.0254
      let displayWidth = width * pixelSize
      let displayHeight = height * pixelSize
      let pixelWidth = pixelSize
      let pixelHeight = pixelSize
      let densityText = null
      if (hasPhysical && unitIsMeter) {
        displayWidth = width / ppuX * cssPxPerMeter
        displayHeight = height / ppuY * cssPxPerMeter
        pixelWidth = displayWidth / Math.max(width, 1)
        pixelHeight = displayHeight / Math.max(height, 1)
        const dpiX = Math.round(ppuX * 0.0254)
        const dpiY = Math.round(ppuY * 0.0254)
        densityText = dpiX === dpiY ? `${dpiX} DPI` : `${dpiX} × ${dpiY} DPI`
      } else if (hasPhysical) {
        displayWidth = width * pixelSize
        displayHeight = height * pixelSize * (ppuX / ppuY)
        pixelWidth = pixelSize
        pixelHeight = pixelSize * (ppuX / ppuY)
        densityText = `pixel aspect ${ppuY}:${ppuX}`
      }

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
          let r = 0
          let g = 0
          let b = 0
          let a = 255
          if (stride === 1) {
            r = bytes[base] ?? 0
            g = r
            b = r
          } else if (stride === 2) {
            r = bytes[base] ?? 0
            g = r
            b = r
            a = bytes[base + 1] ?? 255
          } else if (stride === 3) {
            r = bytes[base] ?? 0
            g = bytes[base + 1] ?? 0
            b = bytes[base + 2] ?? 0
          } else {
            r = bytes[base] ?? 0
            g = bytes[base + 1] ?? 0
            b = bytes[base + 2] ?? 0
            a = bytes[base + 3] ?? 255
          }
          image.data[offset + 0] = r
          image.data[offset + 1] = g
          image.data[offset + 2] = b
          image.data[offset + 3] = a
        }
        ctx.putImageData(image, 0, 0)
      }, [width, height, props.bytes])

      const frameStyle = {
        position: 'relative',
        width: displayWidth,
        height: displayHeight,
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
              backgroundSize: `${pixelWidth}px ${pixelHeight}px`
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
        React.createElement('div', { style: infoStyle },
          densityText ? `${width} × ${height} pixels, ${densityText}` : `${width} × ${height} pixels`),
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
  (BitmapRGB16.widgetProps auroraBitmap16
    (pixelSize := 18)
    (background := "#040b18")
    (caption := some "16-bit aurora bitmap downsampled for canvas display"))

#widget bitmapWidget with
  (testPngWidgetProps)

#widget bitmapWidget with
  (testPngRgbaWidgetProps)

#widget bitmapWidget with
  (testPngGrayWidgetProps)
