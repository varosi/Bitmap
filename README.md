# bitmap

Lean 4 bitmap image utilities with PNG encode/decode support, plus a small widget for visualization.

This library have proofs about:
- putPixel and getPixel correspondence (Bitmap.Lemmas.putPixel_getPixel);
- PNG format encode and decode correspondence (Bitmap.Lemmas.decodeBitmap_encodeBitmap);
- there are no buffer overflows;
- PNG encode and decode are total functions.

## Proof Coverage Limits

The PNG round-trip proofs are encoder-to-decoder proofs for streams produced by this
library. They do not yet prove that the decoder accepts every valid PNG file or every
valid zlib/DEFLATE stream produced by another implementation.

In particular, the dynamic DEFLATE proof currently covers the concrete dynamic block
shape emitted by the library's dynamic-fast encoder: a dynamic block header whose
Huffman tables reconstruct the fixed literal/length and distance tables, followed by
the proven fixed-style payload. This exercises the dynamic table reader and dynamic
block dispatch, but it is not a full DEFLATE specification proof for arbitrary valid
dynamic Huffman tables, all valid code-length repeat encodings, or all valid dynamic
multi-block streams.

Runtime decoding is broader than the current proof boundary: the decoder has a
general dynamic-table reader and compressed-block loop. The missing work is a formal
specification of arbitrary valid dynamic DEFLATE streams and a proof that the runtime
decoder implements that specification.

## Usage

```lean
import Bitmap
```

## Tests

```sh
lake test
```
