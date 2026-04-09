import Bitmap.Lemmas.Png.DynamicBlockProofsReadTables

namespace Bitmaps

namespace Png

set_option maxRecDepth 200000 in
set_option maxHeartbeats 20000000 in
lemma dynamicHeaderCodeLenSyms_writeBits_eq
    (bw : BitWriter) (restBits : Nat) :
    BitWriter.writeBits bw (dynamicHeaderReadBits restBits) dynamicHeaderTableLen =
      BitWriter.writeBits
        (BitWriter.writeBits bw (dynamicHeaderReadBits restBits) 44)
        (dynamicHeaderCodeLenSymsRestBits restBits)
        (2 * dynamicHeaderCodeLenSyms.length) := by
  let prefix44 := dynamicHeaderPrefixBits ||| (dynamicHeaderCodeLenLenBits <<< 14)
  have hprefix44 :
      prefix44 < 2 ^ 44 := by
    native_decide
  have hrepr :
      dynamicHeaderReadBits restBits =
        prefix44 ||| (dynamicHeaderCodeLenSymsRestBits restBits <<< 44) := by
    simp [prefix44, dynamicHeaderReadBits, dynamicHeaderCodeLenLensBits, dynamicHeaderPrefixBits,
      Nat.or_assoc, Nat.shiftLeft_or_distrib, shiftLeft_shiftLeft]
  have hlen :
      dynamicHeaderTableLen = 44 + 2 * dynamicHeaderCodeLenSyms.length := by
    simpa [dynamicHeaderCodeLenLens_length] using dynamicHeaderTableLen_eq_split
  calc
    BitWriter.writeBits bw (dynamicHeaderReadBits restBits) dynamicHeaderTableLen =
      BitWriter.writeBits bw
        (prefix44 ||| (dynamicHeaderCodeLenSymsRestBits restBits <<< 44))
        (44 + 2 * dynamicHeaderCodeLenSyms.length) := by
          rw [hrepr, hlen]
    _ =
      BitWriter.writeBits
        (BitWriter.writeBits bw prefix44 44)
        (dynamicHeaderCodeLenSymsRestBits restBits)
        (2 * dynamicHeaderCodeLenSyms.length) := by
          simpa [prefix44] using
            (writeBits_concat bw prefix44 (dynamicHeaderCodeLenSymsRestBits restBits)
              44 (2 * dynamicHeaderCodeLenSyms.length) hprefix44)
    _ =
      BitWriter.writeBits
        (BitWriter.writeBits bw (dynamicHeaderReadBits restBits) 44)
        (dynamicHeaderCodeLenSymsRestBits restBits)
        (2 * dynamicHeaderCodeLenSyms.length) := by
          have hmod :
              (prefix44 % 2 ^ 44) = dynamicHeaderReadBits restBits % 2 ^ 44 := by
            rw [hrepr]
            simpa using
              (mod_two_pow_or_shift
                (a := prefix44) (b := dynamicHeaderCodeLenSymsRestBits restBits)
                (k := 44) (len := 44) (by decide))
          calc
            BitWriter.writeBits bw prefix44 44 =
              BitWriter.writeBits bw (prefix44 % 2 ^ 44) 44 := by
                simpa using (writeBits_mod bw prefix44 44)
            _ = BitWriter.writeBits bw (dynamicHeaderReadBits restBits % 2 ^ 44) 44 := by
                rw [hmod]
            _ = BitWriter.writeBits bw (dynamicHeaderReadBits restBits) 44 := by
                simpa using (writeBits_mod bw (dynamicHeaderReadBits restBits) 44).symm

end Png

end Bitmaps
