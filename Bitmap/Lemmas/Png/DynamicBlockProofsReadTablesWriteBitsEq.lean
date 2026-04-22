import Bitmap.Lemmas.Png.DynamicBlockProofsReadTables

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
/-- Rewrites the concrete code-length symbol writer into one bulk `writeBits` call for transport lemmas. -/
lemma dynamicHeaderCodeLenSyms_writeBits_eq
    (bw : BitWriter) (restBits : Nat) :
    BitWriter.writeBits bw (dynamicHeaderReadBits restBits) dynamicHeaderTableLen =
      BitWriter.writeBits
        (BitWriter.writeBits bw (dynamicHeaderReadBits restBits) 44)
        (dynamicHeaderCodeLenSymsRestBits restBits)
        (2 * dynamicHeaderCodeLenSyms.length) := by
  have hlen :
      dynamicHeaderTableLen = 44 + 2 * dynamicHeaderCodeLenSyms.length := by
    simpa [dynamicHeaderCodeLenLens_length] using dynamicHeaderTableLen_eq_split
  have hshift :
      dynamicHeaderReadBits restBits >>> 44 = dynamicHeaderCodeLenSymsRestBits restBits := by
    simpa [dynamicHeaderCodeLenLens_length] using dynamicHeaderReadBits_shift44 restBits
  calc
    BitWriter.writeBits bw (dynamicHeaderReadBits restBits) dynamicHeaderTableLen =
      BitWriter.writeBits
        (BitWriter.writeBits bw (dynamicHeaderReadBits restBits) 44)
        (dynamicHeaderCodeLenSymsRestBits restBits)
        (2 * dynamicHeaderCodeLenSyms.length) := by
      rw [hlen]
      simpa [hshift] using
        (writeBits_split bw (dynamicHeaderReadBits restBits) 44
          (2 * dynamicHeaderCodeLenSyms.length))

end Png

end Bitmaps
