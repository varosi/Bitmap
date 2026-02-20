# bitmap

Lean 4 bitmap image utilities with PNG encode/decode support, plus a small widget for visualization.

This library have proofs about:
- putPixel and getPixel correspondence (Bitmap.Lemmas.putPixel_getPixel);
- encode and decode correspondence (Bitmap.Lemmas.decodeBitmap_encodeBitmap);
- there are no buffer overflows.

## Usage

```lean
import Bitmap
```

## Tests

```sh
lake test
```
