import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.Separation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Support.Owner

/-!
# Upper projection support on normalized lower-tail degrees

This file turns the integer support-separation lemma into the corresponding
`Embedding.r = none` statement for Mathlib's upper truncation embedding.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- A degree in the paired lower tail is outside the upper-tail embedding at
cut `cut`. -/
theorem truncGEEmbedding_r_eq_none_of_decompositionLowerTail
    (cut : ℤ)
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r
        (cut - 1 - (lowerTail : ℤ)) =
      none :=
  ComplexShape.Embedding.r_eq_none
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    (cut - 1 - (lowerTail : ℤ))
    (fun upperTail equality =>
      TraceAnalyticMotivicTStructure.decompositionLowerUpperTail_disjoint
        cut
        lowerTail
        upperTail
        equality.symm)

/-- The upper truncation object is degreewise zero on every normalized
lower-tail degree. -/
theorem additiveTruncGE_X_isZero_of_decompositionLowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerTail : ℕ) :
    IsZero
      ((TraceAnalyticMotivicTStructure.additiveTruncGE
          cut
          complex).X (cut - 1 - (lowerTail : ℤ))) :=
  ((complex.truncGE'
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)).isZero_extend_X'
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      (cut - 1 - (lowerTail : ℤ))
      (TraceAnalyticMotivicTStructure.truncGEEmbedding_r_eq_none_of_decompositionLowerTail
        cut
        lowerTail))

/-- The upper truncation projection component is zero on a normalized
lower-tail degree. -/
theorem additiveTruncGEProjectionComponent_of_decompositionLowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerTail : ℕ) :
    TraceAnalyticMotivicTStructure.additiveTruncGEProjectionComponent
        cut
        complex
        (cut - 1 - (lowerTail : ℤ)) =
      0 :=
  TraceAnalyticMotivicTStructure.truncGEProjectionComponent_of_r_eq_none
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    (cut - 1 - (lowerTail : ℤ))
    (TraceAnalyticMotivicTStructure.truncGEEmbedding_r_eq_none_of_decompositionLowerTail
      cut
      lowerTail)

/-- The full upper projection chain map is zero on every component in the
lower tail of the normalized truncation decomposition. -/
theorem additiveTruncGEProjectionMap_f_of_decompositionLowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
        cut
        complex).f
        (cut - 1 - (lowerTail : ℤ)) =
      0 :=
  TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap_f_of_r_eq_none
    cut
    complex
    (cut - 1 - (lowerTail : ℤ))
    (TraceAnalyticMotivicTStructure.truncGEEmbedding_r_eq_none_of_decompositionLowerTail
      cut
      lowerTail)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
