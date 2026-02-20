# bitmap

Lean 4 bitmap image utilities with PNG encode/decode support, plus a small widget for visualization.

This library have proofs about:
- putPixel and getPixel correspondence (Bitmap.Lemmas.putPixel_getPixel);
- PNG format encode and decode correspondence for storage and fixed compression (Bitmap.Lemmas.decodeBitmap_encodeBitmap);
- there are no buffer overflows.

## Usage

```lean
import Bitmap
```

## Tests

```sh
lake test
```
