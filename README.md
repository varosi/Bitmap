# bitmap

Lean 4 bitmap utilities with PNG encode/decode support, plus a small widget for visualization.

This library have proofs about:
- putPixel and getPixel are mirrored
- encode and decode are mirrored
- there are no buffer overflows

## Usage

```lean
import Bitmap
```

## Tests

```sh
lake test
```
