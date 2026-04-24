import Bitmap.Lemmas.Png.DynamicBlockProofsSpec
import Bitmap.Lemmas.Png.DynamicBlockProofsTables

namespace Bitmaps

namespace Png

/-- Packages the concrete dynamic-fast header tables into the generic spec layer so the existing
round-trip theorem remains a regression client of the generalized boundary. -/
def dynamicFastTableSpec : DynamicTableSpec :=
  { litLenLengths := dynamicLitLenLengths
    distLengths := dynamicDistLengths
    litLenTable := fixedLitLenHuffman
    distTable := fixedDistHuffman
    litLenOk := mkHuffman_dynamicLitLenLengths
    distOk := buildDynamicDistTable_of_mkHuffman mkHuffman_dynamicDistLengths }

/-- Shows that the concrete dynamic-fast tables are accepted by the generic dynamic-table
packaging helper without any special casing in the proof layer. -/
lemma dynamicFastTableSpec_ofLengths? :
    DynamicTableSpec.ofLengths? dynamicLitLenLengths dynamicDistLengths = some dynamicFastTableSpec := by
  simpa [dynamicFastTableSpec] using
    (DynamicTableSpec.ofLengths?_mk
      (litLenLengths := dynamicLitLenLengths)
      (distLengths := dynamicDistLengths)
      (litLenTable := fixedLitLenHuffman)
      (distTable := fixedDistHuffman)
      mkHuffman_dynamicLitLenLengths
      (buildDynamicDistTable_of_mkHuffman mkHuffman_dynamicDistLengths))

end Png

end Bitmaps
