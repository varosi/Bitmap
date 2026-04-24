import Bitmap.Lemmas.Png.DynamicBlockProofsPayloadBase
import Bitmap.Lemmas.Png.DynamicBlockProofsPayloadFixedDecodeLen8
import Bitmap.Lemmas.Png.DynamicBlockProofsPayloadFixedDecodeLen9
import Bitmap.Lemmas.Png.DynamicBlockProofsSpec

universe u

namespace Bitmaps

namespace Png

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-- Converts a known literal decode into one step of `decodeCompressedBlockFuel`. -/
lemma decodeCompressedBlockFuel_step_literal_of_decodes_aux
    (fuel : Nat) (litLen dist : Huffman) (br br' : BitReader)
    (out : ByteArray) (sym : Nat)
    (hdecodeSym : litLen.decode br = some (sym, br'))
    (hlit : sym < 256) :
    decodeCompressedBlockFuel (fuel + 1) litLen dist br out =
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym)) := by
  rw [decodeCompressedBlockFuel.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  let k : Nat → BitReader → Option (BitReader × ByteArray) := fun sym br' =>
    if sym < 256 then
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
    else if (sym == 256) = true then
      pure (br', out)
    else if hlen : 257 ≤ sym ∧ sym ≤ 285 then
      let idx := sym - 257
      have hidxle : idx ≤ 28 := by
        dsimp [idx]
        omega
      have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
      have hidxExtra : idx < lengthExtra.size := by
        have hsize : lengthExtra.size = 29 := by decide
        simpa [hsize] using hidxlt
      let extra := Array.getInternal lengthExtra idx hidxExtra
      if hbits : br'.bitIndex + extra ≤ br'.data.size * 8 then
        do
          let (len, br'') := decodeLength sym br' hlen (by simpa using hbits)
          let (distSym, br''') ← dist.decode br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeCompressedBlockFuel fuel litLen dist br'''' out'
            else
              none
          else
            none
      else
        none
    else
      none
  change (match (sym, br') with | (s, r) => k s r) =
    decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
  have hpair : (match (sym, br') with | (s, r) => k s r) = k sym br' := by
    simpa using (match_pair_eta (a := sym) (b := br') (k := k))
  rw [hpair]
  dsimp [k]
  rw [if_pos hlit]

set_option maxRecDepth 200000 in
/-- Replays one low-literal step on the exact reader produced by `writeBits`. -/
lemma decodeCompressedBlockFuel_step_literal_readerAt_writeBits_lo
    (fuel : Nat) (bw : BitWriter) (sym restBits restLen : Nat) (dist : Huffman) (out : ByteArray)
    (h143 : sym ≤ 143) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let code := sym + 48
    let bits := reverseBits code 8
    let bitsTot := bits ||| (restBits <<< 8)
    let lenTot := 8 + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br8 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot 8) bw'.flush
      (by
        have hk : 8 ≤ lenTot := by omega
        simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot 8 lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot 8 hbit)
    decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist br0 out =
      decodeCompressedBlockFuel fuel fixedLitLenHuffman dist br8 (out.push (u8 sym)) := by
  have hdecodeSym :=
    fixedLitLenHuffman_decode_readerAt_writeBits_lo
      (bw := bw) (sym := sym) (restBits := restBits) (restLen := restLen)
      h143 hbit hcur
  have hlit : sym < 256 := by omega
  simpa using
    (decodeCompressedBlockFuel_step_literal_of_decodes_aux
      (fuel := fuel) (litLen := fixedLitLenHuffman) (dist := dist)
      (br := BitWriter.readerAt bw
        (BitWriter.writeBits bw
          ((reverseBits (sym + 48) 8) ||| (restBits <<< 8))
          (8 + restLen)).flush
        (flush_size_writeBits_le bw
          ((reverseBits (sym + 48) 8) ||| (restBits <<< 8))
          (8 + restLen)) hbit)
      (br' := BitWriter.readerAt
        (BitWriter.writeBits bw
          ((reverseBits (sym + 48) 8) ||| (restBits <<< 8)) 8)
        (BitWriter.writeBits bw
          ((reverseBits (sym + 48) 8) ||| (restBits <<< 8))
          (8 + restLen)).flush
        (by
          have hk : 8 ≤ 8 + restLen := by omega
          simpa using
            (flush_size_writeBits_prefix bw
              ((reverseBits (sym + 48) 8) ||| (restBits <<< 8)) 8 (8 + restLen) hk))
        (bitPos_lt_8_writeBits bw
          ((reverseBits (sym + 48) 8) ||| (restBits <<< 8)) 8 hbit))
      (out := out) (sym := sym) (hdecodeSym := by simpa using hdecodeSym) (hlit := hlit))

/-- Replays one literal step for any byte emitted with the fixed literal table. -/
lemma decodeCompressedBlockFuel_step_literal_readerAt_writeBits
    (fuel : Nat) (bw : BitWriter) (sym restBits restLen : Nat) (dist : Huffman) (out : ByteArray)
    (hsym : sym < 256) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let codeLen := fixedLitLenCode sym
    let code := codeLen.1
    let len := codeLen.2
    let bits := reverseBits code len
    let bitsTot := bits ||| (restBits <<< len)
    let lenTot := len + restLen
    let bw' := BitWriter.writeBits bw bitsTot lenTot
    let br0 := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
    let br1 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
      (by
        have hk : len ≤ lenTot := by omega
        simpa [lenTot] using (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
      (bitPos_lt_8_writeBits bw bitsTot len hbit)
    decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist br0 out =
      decodeCompressedBlockFuel fuel fixedLitLenHuffman dist br1 (out.push (u8 sym)) := by
  have hdecodeSym :=
    fixedLitLenHuffman_decode_readerAt_writeBits
      (bw := bw) (sym := sym) (restBits := restBits) (restLen := restLen)
      hsym hbit hcur
  simpa using
    (decodeCompressedBlockFuel_step_literal_of_decodes_aux
      (fuel := fuel) (litLen := fixedLitLenHuffman) (dist := dist)
      (br := BitWriter.readerAt bw
        (BitWriter.writeBits bw
          ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
            (restBits <<< (fixedLitLenCode sym).2))
          ((fixedLitLenCode sym).2 + restLen)).flush
        (flush_size_writeBits_le bw
          ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
            (restBits <<< (fixedLitLenCode sym).2))
          ((fixedLitLenCode sym).2 + restLen)) hbit)
      (br' := BitWriter.readerAt
        (BitWriter.writeBits bw
          ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
            (restBits <<< (fixedLitLenCode sym).2))
          (fixedLitLenCode sym).2)
        (BitWriter.writeBits bw
          ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
            (restBits <<< (fixedLitLenCode sym).2))
          ((fixedLitLenCode sym).2 + restLen)).flush
        (by
          have hk : (fixedLitLenCode sym).2 ≤ (fixedLitLenCode sym).2 + restLen := by omega
          simpa using
            (flush_size_writeBits_prefix bw
              ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
                (restBits <<< (fixedLitLenCode sym).2))
              (fixedLitLenCode sym).2 ((fixedLitLenCode sym).2 + restLen) hk))
        (bitPos_lt_8_writeBits bw
          ((reverseBits (fixedLitLenCode sym).1 (fixedLitLenCode sym).2) |||
            (restBits <<< (fixedLitLenCode sym).2))
          (fixedLitLenCode sym).2 hbit))
      (out := out) (sym := sym) (hdecodeSym := by simpa using hdecodeSym) (hlit := hsym))

/-- General literal-step lemma used after the payload decoder has already identified a byte symbol. -/
lemma decodeCompressedBlockFuel_step_literal_of_decodes
    (fuel : Nat) (litLen dist : Huffman) (br br' : BitReader)
    (out : ByteArray) (sym : Nat)
    (hdecodeSym : litLen.decode br = some (sym, br'))
    (hlit : sym < 256) :
    decodeCompressedBlockFuel (fuel + 1) litLen dist br out =
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym)) := by
  rw [decodeCompressedBlockFuel.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  let k : Nat → BitReader → Option (BitReader × ByteArray) := fun sym br' =>
    if sym < 256 then
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
    else if (sym == 256) = true then
      pure (br', out)
    else if hlen : 257 ≤ sym ∧ sym ≤ 285 then
      let idx := sym - 257
      have hidxle : idx ≤ 28 := by
        dsimp [idx]
        omega
      have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
      have hidxExtra : idx < lengthExtra.size := by
        have hsize : lengthExtra.size = 29 := by decide
        simpa [hsize] using hidxlt
      let extra := Array.getInternal lengthExtra idx hidxExtra
      if hbits : br'.bitIndex + extra ≤ br'.data.size * 8 then
        do
          let (len, br'') := decodeLength sym br' hlen (by simpa using hbits)
          let (distSym, br''') ← dist.decode br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeCompressedBlockFuel fuel litLen dist br'''' out'
            else
              none
          else
            none
      else
        none
    else
      none
  change (match (sym, br') with | (s, r) => k s r) =
    decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
  have hpair : (match (sym, br') with | (s, r) => k s r) = k sym br' := by
    simpa using (match_pair_eta (a := sym) (b := br') (k := k))
  rw [hpair]
  dsimp [k]
  rw [if_pos hlit]

set_option maxRecDepth 200000 in
/-- Converts a known EOB decode into the terminating branch of `decodeCompressedBlockFuel`. -/
lemma decodeCompressedBlockFuel_step_eob_of_decodes
    (fuel : Nat) (litLen dist : Huffman) (br br' : BitReader)
    (out : ByteArray) (sym : Nat)
    (hdecodeSym : litLen.decode br = some (sym, br'))
    (hnotLit : ¬ sym < 256) (heob : (sym == 256) = true) :
    decodeCompressedBlockFuel (fuel + 1) litLen dist br out = some (br', out) := by
  rw [decodeCompressedBlockFuel.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  let k : Nat → BitReader → Option (BitReader × ByteArray) := fun sym br' =>
    if sym < 256 then
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
    else if (sym == 256) = true then
      pure (br', out)
    else if hlen : 257 ≤ sym ∧ sym ≤ 285 then
      let idx := sym - 257
      have hidxle : idx ≤ 28 := by
        dsimp [idx]
        omega
      have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
      have hidxExtra : idx < lengthExtra.size := by
        have hsize : lengthExtra.size = 29 := by decide
        simpa [hsize] using hidxlt
      let extra := Array.getInternal lengthExtra idx hidxExtra
      if hbits : br'.bitIndex + extra ≤ br'.data.size * 8 then
        do
          let (len, br'') := decodeLength sym br' hlen (by simpa using hbits)
          let (distSym, br''') ← dist.decode br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeCompressedBlockFuel fuel litLen dist br'''' out'
            else
              none
          else
            none
      else
        none
    else
      none
  change (match (sym, br') with | (s, r) => k s r) = some (br', out)
  have hpair : (match (sym, br') with | (s, r) => k s r) = k sym br' := by
    simpa using (match_pair_eta (a := sym) (b := br') (k := k))
  rw [hpair]
  dsimp [k]
  rw [if_neg hnotLit, if_pos heob]

set_option maxRecDepth 200000 in
/-- Converts a known match decode into one recursive step of `decodeCompressedBlockFuel`. -/
lemma decodeCompressedBlockFuel_step_match_of_decodes
    (fuel : Nat) (litLen dist : Huffman) (br br' br'' br''' br'''' : BitReader)
    (out out' : ByteArray)
    (sym extra len distSym extraD distance : Nat)
    (hdecodeSym : litLen.decode br = some (sym, br'))
    (hnotLit : ¬ sym < 256)
    (hnotEob : (sym == 256) = false)
    (hsym : 257 ≤ sym ∧ sym ≤ 285)
    (hextra :
      extra =
        Array.getInternal lengthExtra (sym - 257) (by
          have hidxle : sym - 257 ≤ 28 := by omega
          have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
          have hsize : lengthExtra.size = 29 := by decide
          simpa [hsize] using hidxlt))
    (hbits : br'.bitIndex + extra ≤ br'.data.size * 8)
    (hdecodeLen :
      decodeLength sym br' hsym
        (by
          have hbits' : br'.bitIndex +
              lengthExtra[sym - 257]'(by
                have hidxle : sym - 257 ≤ 28 := by omega
                have hidxlt : sym - 257 < 29 := Nat.lt_succ_of_le hidxle
                have hsize : lengthExtra.size = 29 := by decide
                simpa [hsize] using hidxlt) ≤ br'.data.size * 8 := by
            simpa [hextra] using hbits
          simpa using hbits') = (len, br''))
    (hdecodeDistSym : dist.decode br'' = some (distSym, br'''))
    (hdist : distSym < distBases.size)
    (hextraD :
      extraD =
        Array.getInternal distExtra distSym (by
          have hDistExtraSize : distExtra.size = 30 := by decide
          have hDistBasesSize : distBases.size = 30 := by decide
          simpa [hDistExtraSize, hDistBasesSize] using hdist))
    (hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8)
    (hdecodeDist :
      decodeDistance distSym br''' hdist
        (by
          have hbitsD' : br'''.bitIndex +
              distExtra[distSym]'(by
                have hDistExtraSize : distExtra.size = 30 := by decide
                have hDistBasesSize : distBases.size = 30 := by decide
                simpa [hDistExtraSize, hDistBasesSize] using hdist) ≤ br'''.data.size * 8 := by
            simpa [hextraD] using hbitsD
          simpa using hbitsD') = (distance, br''''))
    (hcopy : copyDistance out distance len = some out') :
    decodeCompressedBlockFuel (fuel + 1) litLen dist br out =
      decodeCompressedBlockFuel fuel litLen dist br'''' out' := by
  let recCall := decodeCompressedBlockFuel fuel litLen dist br'''' out'
  change decodeCompressedBlockFuel (fuel + 1) litLen dist br out = recCall
  have hrec : decodeCompressedBlockFuel fuel litLen dist br'''' out' = recCall := rfl
  rw [decodeCompressedBlockFuel.eq_2]
  rw [hdecodeSym]
  rw [option_do_some]
  change
    (if sym < 256 then
      decodeCompressedBlockFuel fuel litLen dist br' (out.push (u8 sym))
    else if (sym == 256) = true then
      pure (br', out)
    else if hlen : 257 ≤ sym ∧ sym ≤ 285 then
      let idx := sym - 257
      have hidxle : idx ≤ 28 := by
        dsimp [idx]
        omega
      have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
      have hidxExtra : idx < lengthExtra.size := by
        have hsize : lengthExtra.size = 29 := by decide
        simpa [hsize] using hidxlt
      let extra := Array.getInternal lengthExtra idx hidxExtra
      if hbits : br'.bitIndex + extra ≤ br'.data.size * 8 then
        do
        let (len, br'') := decodeLength sym br' hlen (by simpa using hbits)
        let (distSym, br''') ← dist.decode br''
        if hdist : distSym < distBases.size then
          let extraD := Array.getInternal distExtra distSym (by
            have hDistExtraSize : distExtra.size = 30 := by decide
            have hDistBasesSize : distBases.size = 30 := by decide
            simpa [hDistExtraSize, hDistBasesSize] using hdist)
          if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
            do
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeCompressedBlockFuel fuel litLen dist br'''' out'
          else
            none
        else
          none
      else
        none
    else
      none) = recCall
  rw [if_neg hnotLit]
  rw [if_neg (by simpa using hnotEob)]
  rw [dif_pos hsym]
  have hLetExtra :
      (let idx := sym - 257
       have hidxle : idx ≤ 28 := by
         dsimp [idx]
         omega
       have hidxlt : idx < 29 := Nat.lt_succ_of_le hidxle
       have hidxExtra : idx < lengthExtra.size := by
         have hsize : lengthExtra.size = 29 := by decide
         simpa [hsize] using hidxlt
       let extra := Array.getInternal lengthExtra idx hidxExtra
       if hbits : br'.bitIndex + extra ≤ br'.data.size * 8 then
         do
           let (len, br'') := decodeLength sym br' hsym (by simpa using hbits)
           let (distSym, br''') ← dist.decode br''
           if hdist : distSym < distBases.size then
             let extraD := Array.getInternal distExtra distSym (by
               have hDistExtraSize : distExtra.size = 30 := by decide
               have hDistBasesSize : distBases.size = 30 := by decide
               simpa [hDistExtraSize, hDistBasesSize] using hdist)
             if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
               do
                 let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
                 let out' ← copyDistance out distance len
                 decodeCompressedBlockFuel fuel litLen dist br'''' out'
             else
               none
           else
             none
       else
         none) =
      (if hbits : br'.bitIndex + extra ≤ br'.data.size * 8 then
        do
          let (len, br'') := decodeLength sym br' hsym (by simpa [hextra] using hbits)
          let (distSym, br''') ← dist.decode br''
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              do
                let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
                let out' ← copyDistance out distance len
                decodeCompressedBlockFuel fuel litLen dist br'''' out'
            else
              none
          else
            none
      else
        none) := by
    simpa [hextra]
  rw [hLetExtra]
  rw [dif_pos hbits]
  rw [hdecodeLen]
  have hPairLen :
      (match (len, br'') with
      | (len, br'') =>
        do
          let __discr ← dist.decode br''
          match __discr with
          | (distSym, br''') =>
            if hdist : distSym < distBases.size then
              let extraD := Array.getInternal distExtra distSym (by
                have hDistExtraSize : distExtra.size = 30 := by decide
                have hDistBasesSize : distBases.size = 30 := by decide
                simpa [hDistExtraSize, hDistBasesSize] using hdist)
              if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
                do
                  let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
                  let out' ← copyDistance out distance len
                  decodeCompressedBlockFuel fuel litLen dist br'''' out'
              else
                none
            else
              none) =
      (do
        let __discr ← dist.decode br''
        match __discr with
        | (distSym, br''') =>
          if hdist : distSym < distBases.size then
            let extraD := Array.getInternal distExtra distSym (by
              have hDistExtraSize : distExtra.size = 30 := by decide
              have hDistBasesSize : distBases.size = 30 := by decide
              simpa [hDistExtraSize, hDistBasesSize] using hdist)
            if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
              do
                let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
                let out' ← copyDistance out distance len
                decodeCompressedBlockFuel fuel litLen dist br'''' out'
            else
              none
          else
            none) := by
    rfl
  rw [hPairLen]
  change
    (do
      let __discr ← dist.decode br''
      match __discr with
      | (distSym, br''') =>
        if hdist : distSym < distBases.size then
          let extraD := Array.getInternal distExtra distSym (by
            have hDistExtraSize : distExtra.size = 30 := by decide
            have hDistBasesSize : distBases.size = 30 := by decide
            simpa [hDistExtraSize, hDistBasesSize] using hdist)
          if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
            do
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeCompressedBlockFuel fuel litLen dist br'''' out'
          else
            none
        else
          none) = recCall
  rw [hdecodeDistSym]
  rw [option_do_some]
  have hPairDistSym :
      (match (distSym, br''') with
      | (distSym, br''') =>
        if hdist : distSym < distBases.size then
          let extraD := Array.getInternal distExtra distSym (by
            have hDistExtraSize : distExtra.size = 30 := by decide
            have hDistBasesSize : distBases.size = 30 := by decide
            simpa [hDistExtraSize, hDistBasesSize] using hdist)
          if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
            do
              let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
              let out' ← copyDistance out distance len
              decodeCompressedBlockFuel fuel litLen dist br'''' out'
          else
            none
        else
          none) =
      (if hdist : distSym < distBases.size then
        let extraD := Array.getInternal distExtra distSym (by
          have hDistExtraSize : distExtra.size = 30 := by decide
          have hDistBasesSize : distBases.size = 30 := by decide
          simpa [hDistExtraSize, hDistBasesSize] using hdist)
        if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
          do
            let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
            let out' ← copyDistance out distance len
            decodeCompressedBlockFuel fuel litLen dist br'''' out'
        else
          none
      else
        none) := by
    rfl
  rw [hPairDistSym]
  change
    (if hdist : distSym < distBases.size then
      let extraD := Array.getInternal distExtra distSym (by
        have hDistExtraSize : distExtra.size = 30 := by decide
        have hDistBasesSize : distBases.size = 30 := by decide
        simpa [hDistExtraSize, hDistBasesSize] using hdist)
      if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
        do
          let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
          let out' ← copyDistance out distance len
          decodeCompressedBlockFuel fuel litLen dist br'''' out'
      else
        none
    else
      none) = recCall
  rw [dif_pos hdist]
  have hLetExtraD :
      (let extraD := Array.getInternal distExtra distSym (by
         have hDistExtraSize : distExtra.size = 30 := by decide
         have hDistBasesSize : distBases.size = 30 := by decide
         simpa [hDistExtraSize, hDistBasesSize] using hdist)
       if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
         do
           let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa using hbitsD)
           let out' ← copyDistance out distance len
           decodeCompressedBlockFuel fuel litLen dist br'''' out'
       else
         none) =
      (if hbitsD : br'''.bitIndex + extraD ≤ br'''.data.size * 8 then
        do
          let (distance, br'''') := decodeDistance distSym br''' hdist (by simpa [hextraD] using hbitsD)
          let out' ← copyDistance out distance len
          decodeCompressedBlockFuel fuel litLen dist br'''' out'
      else
        none) := by
    simpa [hextraD]
  rw [hLetExtraD]
  rw [dif_pos hbitsD]
  rw [hdecodeDist]
  have hPairDist :
      (match (distance, br'''') with
      | (distance, br'''') =>
        do
          let out' ← copyDistance out distance len
          decodeCompressedBlockFuel fuel litLen dist br'''' out') =
      (do
        let out' ← copyDistance out distance len
        decodeCompressedBlockFuel fuel litLen dist br'''' out') := by
    rfl
  rw [hPairDist]
  change
    (do
      let out' ← copyDistance out distance len
      decodeCompressedBlockFuel fuel litLen dist br'''' out') = recCall
  rw [hcopy]
  rw [option_do_some]

set_option maxRecDepth 200000 in
/-- Replays one validated non-terminal payload step packaged by `DynamicPayloadTransition`. -/
lemma decodeCompressedBlockFuel_step_of_transition
    (fuel : Nat) (spec : DynamicTableSpec) (br br' : BitReader)
    (out out' : ByteArray)
    (hstep : DynamicPayloadTransition spec br out br' out') :
    decodeCompressedBlockFuel (fuel + 1) spec.litLenTable spec.distTable br out =
      decodeCompressedBlockFuel fuel spec.litLenTable spec.distTable br' out' := by
  cases hstep with
  | literal sym brStep hdecode hlit =>
      simpa using
        (decodeCompressedBlockFuel_step_literal_of_decodes
          (fuel := fuel) (litLen := spec.litLenTable) (dist := spec.distTable)
          (br := br) (br' := brStep) (out := out) (sym := sym)
          (hdecodeSym := hdecode) (hlit := hlit))
  | match sym extra len distSym extraD distance brStep brLen brDist brNext outNext
      hdecodeSym hnotLit hnotEob hsym hextra hbits hdecodeLen hdecodeDistSym hdist
      hextraD hbitsD hdecodeDist hcopy =>
      simpa using
        (decodeCompressedBlockFuel_step_match_of_decodes
          (fuel := fuel) (litLen := spec.litLenTable) (dist := spec.distTable)
          (br := br) (br' := brStep) (br'' := brLen) (br''' := brDist) (br'''' := brNext)
          (out := out) (out' := outNext) (sym := sym) (extra := extra) (len := len)
          (distSym := distSym) (extraD := extraD) (distance := distance)
          (hdecodeSym := hdecodeSym) (hnotLit := hnotLit) (hnotEob := hnotEob)
          (hsym := hsym) (hextra := hextra) (hbits := hbits) (hdecodeLen := hdecodeLen)
          (hdecodeDistSym := hdecodeDistSym) (hdist := hdist) (hextraD := hextraD)
          (hbitsD := hbitsD) (hdecodeDist := hdecodeDist) (hcopy := hcopy))

set_option maxRecDepth 200000 in
/-- Replays the terminating end-of-block payload step packaged by `DynamicPayloadFinish`. -/
lemma decodeCompressedBlockFuel_step_of_finish
    (fuel : Nat) (spec : DynamicTableSpec) (br br' : BitReader) (out : ByteArray)
    (hstep : DynamicPayloadFinish spec br out br') :
    decodeCompressedBlockFuel (fuel + 1) spec.litLenTable spec.distTable br out =
      some (br', out) := by
  cases hstep with
  | eob sym brStep hdecode hnotLit heob =>
      simpa using
        (decodeCompressedBlockFuel_step_eob_of_decodes
          (fuel := fuel) (litLen := spec.litLenTable) (dist := spec.distTable)
          (br := br) (br' := brStep) (out := out) (sym := sym)
          (hdecodeSym := hdecode) (hnotLit := hnotLit) (heob := heob))

set_option maxRecDepth 200000 in
/-- Runs `decodeCompressedBlockFuel` along any validated dynamic payload trace once the supplied
fuel covers its step count. -/
lemma decodeCompressedBlockFuel_of_trace
    {steps : Nat} {spec : DynamicTableSpec} {br br' : BitReader}
    {out out' : ByteArray}
    (htrace : DynamicPayloadTrace spec steps br out br' out')
    {fuel : Nat} (hfuel : steps ≤ fuel) :
    decodeCompressedBlockFuel fuel spec.litLenTable spec.distTable br out =
      some (br', out') := by
  induction htrace generalizing fuel with
  | finish hfinish =>
      cases fuel with
      | zero =>
          cases hfuel
      | succ fuel =>
          simpa using
            (decodeCompressedBlockFuel_step_of_finish
              (fuel := fuel) (spec := spec) (br := br) (br' := br') (out := out)
              (hstep := hfinish))
  | step hstep hrest ih =>
      cases fuel with
      | zero =>
          cases hfuel
      | succ fuel =>
          have hfuel' : _ := by
            omega
          calc
            decodeCompressedBlockFuel (fuel + 1) spec.litLenTable spec.distTable br out
                = decodeCompressedBlockFuel fuel spec.litLenTable spec.distTable _ _ := by
                    simpa using
                      (decodeCompressedBlockFuel_step_of_transition
                        (fuel := fuel) (spec := spec) (br := br) (br' := _)
                        (out := out) (out' := _) (hstep := hstep))
            _ = some (br', out') := ih hfuel'

set_option maxRecDepth 200000 in
/-- Upgrades a validated payload trace to the top-level block decoder once the standard fuel bound
is known. -/
lemma decodeCompressedBlock_of_trace
    {steps : Nat} {spec : DynamicTableSpec} {br br' : BitReader}
    {out out' : ByteArray}
    (htrace : DynamicPayloadTrace spec steps br out br' out')
    (hfuel : steps ≤ br.data.size * 8 + 1) :
    decodeCompressedBlock spec.litLenTable spec.distTable br out = some (br', out') := by
  unfold decodeCompressedBlock
  exact decodeCompressedBlockFuel_of_trace htrace hfuel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Decodes the fixed-table end-of-block marker when it is written with no trailing payload bits. -/
lemma fixedLitLenHuffman_decode_eobNoTail
    (bw : BitWriter) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    fixedLitLenHuffman.decode (eobNoTailStartReader bw hbit) =
      some (256, eobNoTailAfterReader bw hbit) := by
  let bwAll := BitWriter.writeBits bw 0 7
  let bw1 := BitWriter.writeBits bw 0 1
  let bw2 := BitWriter.writeBits bw 0 2
  let bw3 := BitWriter.writeBits bw 0 3
  let bw4 := BitWriter.writeBits bw 0 4
  let bw5 := BitWriter.writeBits bw 0 5
  let bw6 := BitWriter.writeBits bw 0 6
  let br0 := eobNoTailStartReader bw hbit
  have hsplit1 : bwAll = BitWriter.writeBits bw1 0 6 := by
    simpa [bwAll, bw1] using (writeBits_split bw 0 1 6)
  have hsplit2 : bwAll = BitWriter.writeBits bw2 0 5 := by
    simpa [bwAll, bw2] using (writeBits_split bw 0 2 5)
  have hsplit3 : bwAll = BitWriter.writeBits bw3 0 4 := by
    simpa [bwAll, bw3] using (writeBits_split bw 0 3 4)
  have hsplit4 : bwAll = BitWriter.writeBits bw4 0 3 := by
    simpa [bwAll, bw4] using (writeBits_split bw 0 4 3)
  have hsplit5 : bwAll = BitWriter.writeBits bw5 0 2 := by
    simpa [bwAll, bw5] using (writeBits_split bw 0 5 2)
  have hsplit6 : bwAll = BitWriter.writeBits bw6 0 1 := by
    simpa [bwAll, bw6] using (writeBits_split bw 0 6 1)
  let br1 := BitWriter.readerAt bw1 bwAll.flush
    (by
      simpa [hsplit1] using (flush_size_writeBits_le (bw := bw1) (bits := 0) (len := 6)))
    (by
      simpa [bw1] using bitPos_lt_8_writeBits bw 0 1 hbit)
  let br2 := BitWriter.readerAt bw2 bwAll.flush
    (by
      simpa [hsplit2] using (flush_size_writeBits_le (bw := bw2) (bits := 0) (len := 5)))
    (by
      simpa [bw2] using bitPos_lt_8_writeBits bw 0 2 hbit)
  let br3 := BitWriter.readerAt bw3 bwAll.flush
    (by
      simpa [hsplit3] using (flush_size_writeBits_le (bw := bw3) (bits := 0) (len := 4)))
    (by
      simpa [bw3] using bitPos_lt_8_writeBits bw 0 3 hbit)
  let br4 := BitWriter.readerAt bw4 bwAll.flush
    (by
      simpa [hsplit4] using (flush_size_writeBits_le (bw := bw4) (bits := 0) (len := 3)))
    (by
      simpa [bw4] using bitPos_lt_8_writeBits bw 0 4 hbit)
  let br5 := BitWriter.readerAt bw5 bwAll.flush
    (by
      simpa [hsplit5] using (flush_size_writeBits_le (bw := bw5) (bits := 0) (len := 2)))
    (by
      simpa [bw5] using bitPos_lt_8_writeBits bw 0 5 hbit)
  let br6 := BitWriter.readerAt bw6 bwAll.flush
    (by
      simpa [hsplit6] using (flush_size_writeBits_le (bw := bw6) (bits := 0) (len := 1)))
    (by
      simpa [bw6] using bitPos_lt_8_writeBits bw 0 6 hbit)
  let br7 := eobNoTailAfterReader bw hbit
  have hcur1 : bw1.curClearAbove := by
    simpa [bw1] using curClearAbove_writeBits bw 0 1 hbit hcur
  have hcur2 : bw2.curClearAbove := by
    simpa [bw2] using curClearAbove_writeBits bw 0 2 hbit hcur
  have hcur3 : bw3.curClearAbove := by
    simpa [bw3] using curClearAbove_writeBits bw 0 3 hbit hcur
  have hcur4 : bw4.curClearAbove := by
    simpa [bw4] using curClearAbove_writeBits bw 0 4 hbit hcur
  have hcur5 : bw5.curClearAbove := by
    simpa [bw5] using curClearAbove_writeBits bw 0 5 hbit hcur
  have hcur6 : bw6.curClearAbove := by
    simpa [bw6] using curClearAbove_writeBits bw 0 6 hbit hcur
  have hbound0 : br0.bitIndex + 1 ≤ br0.data.size * 8 := by
    simpa [br0, eobNoTailStartReader, eobNoTailWriter, bwAll, BitWriter.writeBits] using
      (readerAt_writeBits_bound (bw := bw) (bits := 0) (len := 7) (k := 1) (by decide) hbit)
  have hbound1 : br1.bitIndex + 1 ≤ br1.data.size * 8 := by
    simpa [br1, hsplit1] using
      (readerAt_writeBits_bound (bw := bw1) (bits := 0) (len := 6) (k := 1) (by decide)
        (by simpa [bw1] using bitPos_lt_8_writeBits bw 0 1 hbit))
  have hbound2 : br2.bitIndex + 1 ≤ br2.data.size * 8 := by
    simpa [br2, hsplit2] using
      (readerAt_writeBits_bound (bw := bw2) (bits := 0) (len := 5) (k := 1) (by decide)
        (by simpa [bw2] using bitPos_lt_8_writeBits bw 0 2 hbit))
  have hbound3 : br3.bitIndex + 1 ≤ br3.data.size * 8 := by
    simpa [br3, hsplit3] using
      (readerAt_writeBits_bound (bw := bw3) (bits := 0) (len := 4) (k := 1) (by decide)
        (by simpa [bw3] using bitPos_lt_8_writeBits bw 0 3 hbit))
  have hbound4 : br4.bitIndex + 1 ≤ br4.data.size * 8 := by
    simpa [br4, hsplit4] using
      (readerAt_writeBits_bound (bw := bw4) (bits := 0) (len := 3) (k := 1) (by decide)
        (by simpa [bw4] using bitPos_lt_8_writeBits bw 0 4 hbit))
  have hbound5 : br5.bitIndex + 1 ≤ br5.data.size * 8 := by
    simpa [br5, hsplit5] using
      (readerAt_writeBits_bound (bw := bw5) (bits := 0) (len := 2) (k := 1) (by decide)
        (by simpa [bw5] using bitPos_lt_8_writeBits bw 0 5 hbit))
  have hbound6 : br6.bitIndex + 1 ≤ br6.data.size * 8 := by
    simpa [br6, hsplit6] using
      (readerAt_writeBits_bound (bw := bw6) (bits := 0) (len := 1) (k := 1) (by decide)
        (by simpa [bw6] using bitPos_lt_8_writeBits bw 0 6 hbit))
  have hbr0 : br0.bytePos < br0.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br0 (by omega)
  have hbr1 : br1.bytePos < br1.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br1 (by omega)
  have hbr2 : br2.bytePos < br2.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br2 (by omega)
  have hbr3 : br3.bytePos < br3.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br3 (by omega)
  have hbr4 : br4.bytePos < br4.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br4 (by omega)
  have hbr5 : br5.bytePos < br5.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br5 (by omega)
  have hbr6 : br6.bytePos < br6.data.size := by
    exact bytePos_lt_of_bitIndex_lt_dataBits br6 (by omega)
  have hread0 :
      br0.readBit = (0, br1) := by
    simpa [br0, br1, eobNoTailStartReader, eobNoTailWriter, bwAll, bw1, BitWriter.writeBits, hsplit1] using
      (readBit_readerAt_writeBits (bw := bw) (bits := 0) (len := 7) hbit hcur (by decide))
  have hread1 :
      br1.readBit = (0, br2) := by
    simpa [br1, br2, bw1, bw2, BitWriter.writeBits, hsplit1, hsplit2] using
      (readBit_readerAt_writeBits (bw := bw1) (bits := 0) (len := 6)
        (by simpa [bw1] using bitPos_lt_8_writeBits bw 0 1 hbit) hcur1 (by decide))
  have hread2 :
      br2.readBit = (0, br3) := by
    simpa [br2, br3, bw2, bw3, BitWriter.writeBits, hsplit2, hsplit3] using
      (readBit_readerAt_writeBits (bw := bw2) (bits := 0) (len := 5)
        (by simpa [bw2] using bitPos_lt_8_writeBits bw 0 2 hbit) hcur2 (by decide))
  have hread3 :
      br3.readBit = (0, br4) := by
    simpa [br3, br4, bw3, bw4, BitWriter.writeBits, hsplit3, hsplit4] using
      (readBit_readerAt_writeBits (bw := bw3) (bits := 0) (len := 4)
        (by simpa [bw3] using bitPos_lt_8_writeBits bw 0 3 hbit) hcur3 (by decide))
  have hread4 :
      br4.readBit = (0, br5) := by
    simpa [br4, br5, bw4, bw5, BitWriter.writeBits, hsplit4, hsplit5] using
      (readBit_readerAt_writeBits (bw := bw4) (bits := 0) (len := 3)
        (by simpa [bw4] using bitPos_lt_8_writeBits bw 0 4 hbit) hcur4 (by decide))
  have hread5 :
      br5.readBit = (0, br6) := by
    simpa [br5, br6, bw5, bw6, BitWriter.writeBits, hsplit5, hsplit6] using
      (readBit_readerAt_writeBits (bw := bw5) (bits := 0) (len := 2)
        (by simpa [bw5] using bitPos_lt_8_writeBits bw 0 5 hbit) hcur5 (by decide))
  have hread6 :
      br6.readBit = (0, br7) := by
    simpa [br6, br7, eobNoTailAfterReader, eobNoTailWriter, bwAll, bw6, BitWriter.writeBits, hsplit6] using
      (readBit_readerAt_writeBits (bw := bw6) (bits := 0) (len := 1)
        (by simpa [bw6] using bitPos_lt_8_writeBits bw 0 6 hbit) hcur6 (by decide))
  have htable1 : 1 < fixedLitLenHuffman.table.size := by native_decide
  have htable2 : 2 < fixedLitLenHuffman.table.size := by native_decide
  have htable3 : 3 < fixedLitLenHuffman.table.size := by native_decide
  have htable4 : 4 < fixedLitLenHuffman.table.size := by native_decide
  have htable5 : 5 < fixedLitLenHuffman.table.size := by native_decide
  have htable6 : 6 < fixedLitLenHuffman.table.size := by native_decide
  have htable7 : 7 < fixedLitLenHuffman.table.size := by native_decide
  have hcode1 : 0 < (Array.getInternal fixedLitLenHuffman.table 1 htable1).size := by
    have hcode1' :
        0 < (Array.getInternal fixedLitLenHuffman.table 1
          (by native_decide : 1 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode1'
  have hcode2 : 0 < (Array.getInternal fixedLitLenHuffman.table 2 htable2).size := by
    have hcode2' :
        0 < (Array.getInternal fixedLitLenHuffman.table 2
          (by native_decide : 2 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode2'
  have hcode3 : 0 < (Array.getInternal fixedLitLenHuffman.table 3 htable3).size := by
    have hcode3' :
        0 < (Array.getInternal fixedLitLenHuffman.table 3
          (by native_decide : 3 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode3'
  have hcode4 : 0 < (Array.getInternal fixedLitLenHuffman.table 4 htable4).size := by
    have hcode4' :
        0 < (Array.getInternal fixedLitLenHuffman.table 4
          (by native_decide : 4 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode4'
  have hcode5 : 0 < (Array.getInternal fixedLitLenHuffman.table 5 htable5).size := by
    have hcode5' :
        0 < (Array.getInternal fixedLitLenHuffman.table 5
          (by native_decide : 5 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode5'
  have hcode6 : 0 < (Array.getInternal fixedLitLenHuffman.table 6 htable6).size := by
    have hcode6' :
        0 < (Array.getInternal fixedLitLenHuffman.table 6
          (by native_decide : 6 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode6'
  have hcode7 : 0 < (Array.getInternal fixedLitLenHuffman.table 7 htable7).size := by
    have hcode7' :
        0 < (Array.getInternal fixedLitLenHuffman.table 7
          (by native_decide : 7 < fixedLitLenHuffman.table.size)).size := by
      native_decide
    simpa using hcode7'
  have hrow1 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 1 htable1) 0 hcode1 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 1) (code := 0) (by decide) (by decide) hcode1
  have hrow2 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 2 htable2) 0 hcode2 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 2) (code := 0) (by decide) (by decide) hcode2
  have hrow3 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 3 htable3) 0 hcode3 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 3) (code := 0) (by decide) (by decide) hcode3
  have hrow4 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 4 htable4) 0 hcode4 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 4) (code := 0) (by decide) (by decide) hcode4
  have hrow5 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 5 htable5) 0 hcode5 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 5) (code := 0) (by decide) (by decide) hcode5
  have hrow6 : Array.getInternal (Array.getInternal fixedLitLenHuffman.table 6 htable6) 0 hcode6 = none := by
    exact fixedLitLenHuffman_small_row_get_none (len := 6) (code := 0) (by decide) (by decide) hcode6
  have hrow7 :
      Array.getInternal (Array.getInternal fixedLitLenHuffman.table 7 htable7) 0 hcode7 = some 256 := by
    simpa using fixedLitLenHuffman_row7_get_eob
  have hstep0 :
      fixedLitLenHuffman.decode br0 =
        Huffman.decodeFuel fixedLitLenHuffman 8 0 1 br1 := by
    unfold Huffman.decode
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 8) (code := 0) (len := 0)
        (br := br0) (br' := br1) (bit := 0)
        (hbyte := hbr0) (hread := hread0) (htable := htable1) (hcode := hcode1) (hrow := hrow1))
  have hstep1 :
      Huffman.decodeFuel fixedLitLenHuffman 8 0 1 br1 =
        Huffman.decodeFuel fixedLitLenHuffman 7 0 2 br2 := by
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 7) (code := 0) (len := 1)
        (br := br1) (br' := br2) (bit := 0)
        (hbyte := hbr1) (hread := hread1) (htable := htable2) (hcode := hcode2) (hrow := hrow2))
  have hstep2 :
      Huffman.decodeFuel fixedLitLenHuffman 7 0 2 br2 =
        Huffman.decodeFuel fixedLitLenHuffman 6 0 3 br3 := by
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 6) (code := 0) (len := 2)
        (br := br2) (br' := br3) (bit := 0)
        (hbyte := hbr2) (hread := hread2) (htable := htable3) (hcode := hcode3) (hrow := hrow3))
  have hstep3 :
      Huffman.decodeFuel fixedLitLenHuffman 6 0 3 br3 =
        Huffman.decodeFuel fixedLitLenHuffman 5 0 4 br4 := by
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 5) (code := 0) (len := 3)
        (br := br3) (br' := br4) (bit := 0)
        (hbyte := hbr3) (hread := hread3) (htable := htable4) (hcode := hcode4) (hrow := hrow4))
  have hstep4 :
      Huffman.decodeFuel fixedLitLenHuffman 5 0 4 br4 =
        Huffman.decodeFuel fixedLitLenHuffman 4 0 5 br5 := by
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 4) (code := 0) (len := 4)
        (br := br4) (br' := br5) (bit := 0)
        (hbyte := hbr4) (hread := hread4) (htable := htable5) (hcode := hcode5) (hrow := hrow5))
  have hstep5 :
      Huffman.decodeFuel fixedLitLenHuffman 4 0 5 br5 =
        Huffman.decodeFuel fixedLitLenHuffman 3 0 6 br6 := by
    simpa using
      (Huffman.decodeFuel_step_none (h := fixedLitLenHuffman) (fuel := 3) (code := 0) (len := 5)
        (br := br5) (br' := br6) (bit := 0)
        (hbyte := hbr5) (hread := hread5) (htable := htable6) (hcode := hcode6) (hrow := hrow6))
  have hstep6 :
      Huffman.decodeFuel fixedLitLenHuffman 3 0 6 br6 = some (256, br7) := by
    simpa using
      (Huffman.decodeFuel_step_some (h := fixedLitLenHuffman) (fuel := 2) (code := 0) (len := 6)
        (br := br6) (br' := br7) (bit := 0) (sym := 256)
        (hbyte := hbr6) (hread := hread6) (htable := htable7) (hcode := hcode7) (hrow := hrow7))
  calc
    fixedLitLenHuffman.decode br0 = Huffman.decodeFuel fixedLitLenHuffman 8 0 1 br1 := hstep0
    _ = Huffman.decodeFuel fixedLitLenHuffman 7 0 2 br2 := hstep1
    _ = Huffman.decodeFuel fixedLitLenHuffman 6 0 3 br3 := hstep2
    _ = Huffman.decodeFuel fixedLitLenHuffman 5 0 4 br4 := hstep3
    _ = Huffman.decodeFuel fixedLitLenHuffman 4 0 5 br5 := hstep4
    _ = Huffman.decodeFuel fixedLitLenHuffman 3 0 6 br6 := hstep5
    _ = some (256, br7) := hstep6

set_option maxRecDepth 200000 in
/-- Replays the terminating EOB step of `decodeCompressedBlockFuel` on the no-tail reader. -/
lemma decodeCompressedBlockFuel_step_eob_eobNoTail
    (fuel : Nat) (bw : BitWriter) (dist : Huffman) (out : ByteArray)
    (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist (eobNoTailStartReader bw hbit) out =
      some (eobNoTailAfterReader bw hbit, out) := by
  have hdecodeSym : fixedLitLenHuffman.decode (eobNoTailStartReader bw hbit) =
      some (256, eobNoTailAfterReader bw hbit) := by
    exact fixedLitLenHuffman_decode_eobNoTail (bw := bw) (hbit := hbit) (hcur := hcur)
  have hnotLit : ¬ (256 : Nat) < 256 := by decide
  have heob : ((256 : Nat) == 256) = true := by decide
  simpa using
    (decodeCompressedBlockFuel_step_eob_of_decodes
      (fuel := fuel) (litLen := fixedLitLenHuffman) (dist := dist)
      (br := eobNoTailStartReader bw hbit) (br' := eobNoTailAfterReader bw hbit)
      (out := out) (sym := 256) (hdecodeSym := hdecodeSym) (hnotLit := hnotLit) (heob := heob))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Builds the generic payload trace for the fixed-literal regression stream emitted by
`fixedLitBitsEob`. -/
lemma fixedLitBitsEob_trace_spec
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (spec : DynamicTableSpec)
    (out : ByteArray) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    (hlit : spec.litLenTable = fixedLitLenHuffman) :
    let bitsLen := fixedLitBitsEob data i
    let bits := bitsLen.1
    let len := bitsLen.2
    let bw' := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
    DynamicPayloadTrace spec (data.size - i + 1) br out
      (BitWriter.readerAt (BitWriter.writeBits bw bits len) bw'.flush
        (by
          simpa [bw'] using
            (le_rfl : (BitWriter.writeBits bw bits len).flush.size ≤
              (BitWriter.writeBits bw bits len).flush.size))
        (bitPos_lt_8_writeBits bw bits len hbit))
      (byteArrayFromArray data i out) := by
  classical
  have hk :
      ∀ k, ∀ i bw out (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove), data.size - i = k →
        let bitsLen := fixedLitBitsEob data i
        let bits := bitsLen.1
        let len := bitsLen.2
        let bw' := BitWriter.writeBits bw bits len
        let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
        DynamicPayloadTrace spec (k + 1) br out
          (BitWriter.readerAt (BitWriter.writeBits bw bits len) bw'.flush
            (by
              simpa [bw'] using
                (le_rfl : (BitWriter.writeBits bw bits len).flush.size ≤
                  (BitWriter.writeBits bw bits len).flush.size))
            (bitPos_lt_8_writeBits bw bits len hbit))
          (byteArrayFromArray data i out) := by
    intro k
    induction k with
    | zero =>
        intro i bw out hbit hcur hk
        have hle : data.size ≤ i := Nat.le_of_sub_eq_zero hk
        have hlt : ¬ i < data.size := not_lt_of_ge hle
        have hdecodeSym :
            spec.litLenTable.decode (eobNoTailStartReader bw hbit) =
              some (256, eobNoTailAfterReader bw hbit) := by
          simpa [hlit] using
            (fixedLitLenHuffman_decode_eobNoTail (bw := bw) (hbit := hbit) (hcur := hcur))
        have hfinish :
            DynamicPayloadFinish spec (eobNoTailStartReader bw hbit) out
              (eobNoTailAfterReader bw hbit) := by
          exact DynamicPayloadFinish.eob
            (spec := spec) (br := eobNoTailStartReader bw hbit) (out := out)
            (sym := 256) (br' := eobNoTailAfterReader bw hbit)
            hdecodeSym (by decide) (by decide)
        simpa [fixedLitBitsEob, hlt, byteArrayFromArray, eobNoTailWriter,
            eobNoTailStartReader, eobNoTailAfterReader] using
          (DynamicPayloadTrace.finish (spec := spec) hfinish)
    | succ k ih =>
        intro i bw out hbit hcur hk
        have hlt : i < data.size := by
          have hpos : 0 < data.size - i := by omega
          exact (Nat.sub_pos_iff_lt).1 hpos
        have hk' : data.size - (i + 1) = k := by omega
        let b := data[i]
        let codeLen := fixedLitLenCode b.toNat
        let code := codeLen.1
        let len := codeLen.2
        let bits := reverseBits code len
        let rest := fixedLitBitsEob data (i + 1)
        let restBits := rest.1
        let restLen := rest.2
        let bitsTot := bits ||| (restBits <<< len)
        let lenTot := len + restLen
        let bw' := BitWriter.writeBits bw bitsTot lenTot
        let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
        let br1 := BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
          (by
            have hklen : len ≤ lenTot := by omega
            simpa [bw', lenTot] using
              (flush_size_writeBits_prefix bw bitsTot len lenTot hklen))
          (bitPos_lt_8_writeBits bw bitsTot len hbit)
        have hbitsLen : fixedLitBitsEob data i = (bitsTot, lenTot) := by
          rw [fixedLitBitsEob]
          simp [hlt, bitsTot, lenTot, b, codeLen, code, len, bits, rest, restBits, restLen]
        have hsym : b.toNat < 256 := by
          simpa using (UInt8.toNat_lt b)
        have hdecodeSym :
            spec.litLenTable.decode br = some (b.toNat, br1) := by
          simpa [hlit, br, br1, codeLen, code, len, bits, rest, restBits, restLen, bitsTot, lenTot,
            bw'] using
            (fixedLitLenHuffman_decode_readerAt_writeBits
              (bw := bw) (sym := b.toNat) (restBits := restBits) (restLen := restLen)
              hsym hbit hcur)
        have hstep :
            DynamicPayloadTransition spec br out br1 (out.push (u8 b.toNat)) := by
          exact DynamicPayloadTransition.literal
            (spec := spec) (br := br) (out := out)
            (sym := b.toNat) (br' := br1) hdecodeSym hsym
        have hbitsLt : bits < 2 ^ len := by
          simpa [bits] using (reverseBits_lt code len)
        have hconcat :
            BitWriter.writeBits bw bitsTot lenTot =
              BitWriter.writeBits (BitWriter.writeBits bw bits len) restBits restLen := by
          simpa [bitsTot, lenTot] using (writeBits_concat bw bits restBits len restLen hbitsLt)
        have hmod : bitsTot % 2 ^ len = bits := by
          have hmod' : bitsTot % 2 ^ len = bits % 2 ^ len := by
            simpa [bitsTot] using
              (mod_two_pow_or_shift (a := bits) (b := restBits) (k := len) (len := len) (hk := le_rfl))
          have hbitsmod : bits % 2 ^ len = bits := Nat.mod_eq_of_lt hbitsLt
          simpa [hbitsmod] using hmod'
        have hwriteBits : BitWriter.writeBits bw bitsTot len = BitWriter.writeBits bw bits len := by
          calc
            BitWriter.writeBits bw bitsTot len
                = BitWriter.writeBits bw (bitsTot % 2 ^ len) len := by
                    simpa using (writeBits_mod bw bitsTot len)
            _ = BitWriter.writeBits bw bits len := by
                    simp [hmod]
        have hrest :=
          ih (i := i + 1) (bw := BitWriter.writeBits bw bits len)
            (out := out.push (u8 b.toNat))
            (hbit := bitPos_lt_8_writeBits bw bits len hbit)
            (hcur := curClearAbove_writeBits bw bits len hbit hcur) hk'
        have hrest' :
            DynamicPayloadTrace spec (k + 1) br1 (out.push (u8 b.toNat))
              (BitWriter.readerAt (BitWriter.writeBits bw bitsTot lenTot) bw'.flush
                (by
                  simpa [bw'] using
                    (le_rfl : (BitWriter.writeBits bw bitsTot lenTot).flush.size ≤
                      (BitWriter.writeBits bw bitsTot lenTot).flush.size))
                (bitPos_lt_8_writeBits bw bitsTot lenTot hbit))
              (byteArrayFromArray data (i + 1) (out.push (u8 b.toNat))) := by
          simpa [bitsTot, lenTot, bw', hconcat, hwriteBits] using hrest
        have hstepOut :
            byteArrayFromArray data i out =
              byteArrayFromArray data (i + 1) (out.push (u8 b.toNat)) := by
          rw [byteArrayFromArray_unfold]
          simp [hlt, b, u8]
        simpa [hbitsLen, bw', br, hstepOut, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (DynamicPayloadTrace.step (spec := spec) (hstep := hstep) (hrest := hrest'))
  let bitsLen := fixedLitBitsEob data i
  let bits := bitsLen.1
  let len := bitsLen.2
  let bw' := BitWriter.writeBits bw bits len
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
  simpa [bitsLen, bits, len, bw', br] using
    (hk (data.size - i) i bw out hbit hcur rfl)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Proves that decoding the fixed literal payload followed by EOB reconstructs the original bytes. -/
lemma decodeCompressedBlock_fixedLitBitsEob
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (dist : Huffman)
    (out : ByteArray) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove) :
    let bitsLen := fixedLitBitsEob data i
    let bits := bitsLen.1
    let len := bitsLen.2
    let bw' := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
    decodeCompressedBlock fixedLitLenHuffman dist br out =
      some
        (BitWriter.readerAt (BitWriter.writeBits bw bits len) bw'.flush
          (by
            simpa [bw'] using
              (le_rfl : (BitWriter.writeBits bw bits len).flush.size ≤
                (BitWriter.writeBits bw bits len).flush.size))
          (bitPos_lt_8_writeBits bw bits len hbit),
        byteArrayFromArray data i out) := by
  classical
  have hk :
      ∀ k, ∀ i bw out (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove), data.size - i = k →
        ∀ fuel, k + 1 ≤ fuel →
          let bitsLen := fixedLitBitsEob data i
          let bits := bitsLen.1
          let len := bitsLen.2
          let bw' := BitWriter.writeBits bw bits len
          let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
          decodeCompressedBlockFuel fuel fixedLitLenHuffman dist br out =
            some
              (BitWriter.readerAt (BitWriter.writeBits bw bits len) bw'.flush
                (by
                  simpa [bw'] using
                    (le_rfl : (BitWriter.writeBits bw bits len).flush.size ≤
                      (BitWriter.writeBits bw bits len).flush.size))
                (bitPos_lt_8_writeBits bw bits len hbit),
              byteArrayFromArray data i out) := by
    intro k
    induction k with
    | zero =>
        intro i bw out hbit hcur hk fuel hfuel
        cases fuel with
        | zero =>
            have : (1 : Nat) ≤ 0 := by simpa using hfuel
            exact (False.elim (Nat.not_succ_le_zero 0 this))
        | succ fuel =>
            have hle : data.size ≤ i := Nat.le_of_sub_eq_zero hk
            have hlt : ¬ i < data.size := not_lt_of_ge hle
            simpa [fixedLitBitsEob, hlt, byteArrayFromArray, eobNoTailWriter,
                eobNoTailStartReader, eobNoTailAfterReader] using
              (decodeCompressedBlockFuel_step_eob_eobNoTail
                (fuel := fuel) (bw := bw) (dist := dist) (out := out) hbit hcur)
    | succ k ih =>
        intro i bw out hbit hcur hk fuel hfuel
        cases fuel with
        | zero =>
            have : (k + 2) ≤ 0 := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfuel
            exact (False.elim (Nat.not_succ_le_zero _ this))
        | succ fuel =>
            have hlt : i < data.size := by
              have hpos : 0 < data.size - i := by omega
              exact (Nat.sub_pos_iff_lt).1 hpos
            have hk' : data.size - (i + 1) = k := by omega
            let b := data[i]
            let codeLen := fixedLitLenCode b.toNat
            let code := codeLen.1
            let len := codeLen.2
            let bits := reverseBits code len
            let rest := fixedLitBitsEob data (i + 1)
            let restBits := rest.1
            let restLen := rest.2
            let bitsTot := bits ||| (restBits <<< len)
            let lenTot := len + restLen
            let bw' := BitWriter.writeBits bw bitsTot lenTot
            let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bitsTot lenTot) hbit
            have hbitsLen : fixedLitBitsEob data i = (bitsTot, lenTot) := by
              rw [fixedLitBitsEob]
              simp [hlt, bitsTot, lenTot, b, codeLen, code, len, bits, rest, restBits, restLen]
            have hsym : b.toNat < 256 := by
              simpa using (UInt8.toNat_lt b)
            have hdecode :=
              decodeCompressedBlockFuel_step_literal_readerAt_writeBits
                (fuel := fuel) (bw := bw) (sym := b.toNat)
                (restBits := restBits) (restLen := restLen)
                (dist := dist) (out := out) hsym hbit hcur
            have hbits : bits < 2 ^ len := by
              simpa [bits] using (reverseBits_lt code len)
            have hconcat :
                BitWriter.writeBits bw bitsTot lenTot =
                  BitWriter.writeBits (BitWriter.writeBits bw bits len) restBits restLen := by
              simpa [bitsTot, lenTot] using (writeBits_concat bw bits restBits len restLen hbits)
            have hmod : bitsTot % 2 ^ len = bits := by
              have hmod' : bitsTot % 2 ^ len = bits % 2 ^ len := by
                simpa [bitsTot] using
                  (mod_two_pow_or_shift (a := bits) (b := restBits) (k := len) (len := len) (hk := le_rfl))
              have hbitsmod : bits % 2 ^ len = bits := Nat.mod_eq_of_lt hbits
              simpa [hbitsmod] using hmod'
            have hwriteBits : BitWriter.writeBits bw bitsTot len = BitWriter.writeBits bw bits len := by
              calc
                BitWriter.writeBits bw bitsTot len
                    = BitWriter.writeBits bw (bitsTot % 2 ^ len) len := by
                        simpa using (writeBits_mod bw bitsTot len)
                _ = BitWriter.writeBits bw bits len := by
                        simp [hmod]
            have hih :=
              ih (i := i + 1) (bw := BitWriter.writeBits bw bits len)
                (out := out.push (u8 b.toNat))
                (hbit := bitPos_lt_8_writeBits bw bits len hbit)
                (hcur := curClearAbove_writeBits bw bits len hbit hcur) hk' fuel (by
                  have : k + 2 ≤ Nat.succ fuel := by
                    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfuel
                  exact Nat.succ_le_succ_iff.mp this)
            have hih' :
                decodeCompressedBlockFuel fuel fixedLitLenHuffman dist
                    (BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
                      (by
                        have hk : len ≤ lenTot := by omega
                        simpa [bw', lenTot] using
                          (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
                      (bitPos_lt_8_writeBits bw bitsTot len hbit))
                    (out.push (u8 b.toNat)) =
                  some
                    (BitWriter.readerAt (BitWriter.writeBits bw bitsTot lenTot) bw'.flush
                      (by
                        simpa [bw'] using
                          (le_rfl : (BitWriter.writeBits bw bitsTot lenTot).flush.size ≤
                            (BitWriter.writeBits bw bitsTot lenTot).flush.size))
                      (bitPos_lt_8_writeBits bw bitsTot lenTot hbit),
                    byteArrayFromArray data (i + 1) (out.push (u8 b.toNat))) := by
              simpa [bitsTot, lenTot, bw', hconcat, hwriteBits] using hih
            have hdecode' :
                decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist br out =
                  decodeCompressedBlockFuel fuel fixedLitLenHuffman dist
                    (BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
                      (by
                        have hk : len ≤ lenTot := by omega
                        simpa [bw', lenTot] using
                          (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
                      (bitPos_lt_8_writeBits bw bitsTot len hbit))
                    (out.push (u8 b.toNat)) := by
              simpa [bitsTot, lenTot, bw', br, codeLen, code, len, bits, rest, restBits, restLen] using hdecode
            have hstep :
                byteArrayFromArray data i out =
                  byteArrayFromArray data (i + 1) (out.push (u8 b.toNat)) := by
              rw [byteArrayFromArray_unfold]
              simp [hlt, b, u8]
            have hcalc :
                decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist br out =
                  some
                    (BitWriter.readerAt (BitWriter.writeBits bw bitsTot lenTot) bw'.flush
                      (by
                        simpa [bw'] using
                          (le_rfl : (BitWriter.writeBits bw bitsTot lenTot).flush.size ≤
                            (BitWriter.writeBits bw bitsTot lenTot).flush.size))
                      (bitPos_lt_8_writeBits bw bitsTot lenTot hbit),
                    byteArrayFromArray data i out) := by
              calc
                decodeCompressedBlockFuel (fuel + 1) fixedLitLenHuffman dist br out
                    = decodeCompressedBlockFuel fuel fixedLitLenHuffman dist
                        (BitWriter.readerAt (BitWriter.writeBits bw bitsTot len) bw'.flush
                          (by
                            have hk : len ≤ lenTot := by omega
                            simpa [bw', lenTot] using
                              (flush_size_writeBits_prefix bw bitsTot len lenTot hk))
                          (bitPos_lt_8_writeBits bw bitsTot len hbit))
                        (out.push (u8 b.toNat)) := hdecode'
                _ = some
                      (BitWriter.readerAt (BitWriter.writeBits bw bitsTot lenTot) bw'.flush
                        (by
                          simpa [bw'] using
                            (le_rfl : (BitWriter.writeBits bw bitsTot lenTot).flush.size ≤
                              (BitWriter.writeBits bw bitsTot lenTot).flush.size))
                        (bitPos_lt_8_writeBits bw bitsTot lenTot hbit),
                      byteArrayFromArray data (i + 1) (out.push (u8 b.toNat))) := hih'
                _ = some
                      (BitWriter.readerAt (BitWriter.writeBits bw bitsTot lenTot) bw'.flush
                        (by
                          simpa [bw'] using
                            (le_rfl : (BitWriter.writeBits bw bitsTot lenTot).flush.size ≤
                              (BitWriter.writeBits bw bitsTot lenTot).flush.size))
                        (bitPos_lt_8_writeBits bw bitsTot lenTot hbit),
                      byteArrayFromArray data i out) := by
                    simp [hstep]
            simpa [hbitsLen, bw', br] using hcalc
  let bitsLen := fixedLitBitsEob data i
  let bits := bitsLen.1
  let len := bitsLen.2
  let bw' := BitWriter.writeBits bw bits len
  let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
  have hlen_ge : data.size - i + 1 ≤ len := by
    simpa [bitsLen, len] using (fixedLitBitsEob_len_ge (data := data) (i := i))
  have hlen_le : len ≤ br.data.size * 8 := by
    have hlen_le_bitcount : len ≤ bw'.bitCount := by
      have h := Nat.le_add_left len bw.bitCount
      simpa [bw', bitCount_writeBits, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have hbitcount_le : bw'.bitCount ≤ bw'.flush.size * 8 := by
      exact flush_size_mul_ge_bitCount (bw := bw') (hbit := bw'.hbit)
    have hlen_le' : len ≤ bw'.flush.size * 8 := le_trans hlen_le_bitcount hbitcount_le
    simpa [br] using hlen_le'
  have hfuel : data.size - i + 1 ≤ br.data.size * 8 + 1 := by
    omega
  have hmain := hk (data.size - i) i bw out hbit hcur rfl (br.data.size * 8 + 1) hfuel
  unfold decodeCompressedBlock
  simpa [bitsLen, bits, len, bw', br] using hmain

/-- Repackages the fixed-literal payload round-trip theorem through `DynamicTableSpec`. The
distance table is unused on this payload shape, so the literal-only empty-distance case is
covered automatically as soon as the literal/length table is validated. -/
lemma decodeCompressedBlock_fixedLitBitsEob_spec
    (data : Array UInt8) (i : Nat) (bw : BitWriter) (spec : DynamicTableSpec)
    (out : ByteArray) (hbit : bw.bitPos < 8) (hcur : bw.curClearAbove)
    (hlit : spec.litLenTable = fixedLitLenHuffman) :
    let bitsLen := fixedLitBitsEob data i
    let bits := bitsLen.1
    let len := bitsLen.2
    let bw' := BitWriter.writeBits bw bits len
    let br := BitWriter.readerAt bw bw'.flush (flush_size_writeBits_le bw bits len) hbit
    decodeCompressedBlock spec.litLenTable spec.distTable br out =
      some
        (BitWriter.readerAt (BitWriter.writeBits bw bits len) bw'.flush
          (by
            simpa [bw'] using
              (le_rfl : (BitWriter.writeBits bw bits len).flush.size ≤
                (BitWriter.writeBits bw bits len).flush.size))
          (bitPos_lt_8_writeBits bw bits len hbit),
        byteArrayFromArray data i out) := by
  subst hlit
  simpa using
    (decodeCompressedBlock_fixedLitBitsEob
      (data := data) (i := i) (bw := bw) (dist := spec.distTable)
      (out := out) hbit hcur)

end Png

end Bitmaps
