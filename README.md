# bitmap

Lean 4 bitmap utilities with PNG encode/decode support, plus a small widget for visualization.

This library have proofs about:
- putPixel and getPixel are mirrored (Bitmap.Lemmas.putPixel_getPixel);
- encode and decode are mirrored (Bitmap.Lemmas.decodeBitmap_encodeBitmap);
- there are no buffer overflows.

## Usage

```lean
import Bitmap
```

## Tests

```sh
lake test
```
