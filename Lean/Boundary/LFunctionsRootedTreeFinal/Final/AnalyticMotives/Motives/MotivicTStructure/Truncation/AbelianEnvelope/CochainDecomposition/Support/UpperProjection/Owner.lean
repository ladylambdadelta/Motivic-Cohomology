import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.UpperProjection.Owner

/-!
# Abelian-envelope upper projection support

The normalized lower-tail degrees are outside the paired upper-tail embedding.
Therefore the abelian-envelope upper projection has zero components on those
degrees.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The abelian-envelope upper truncation object is zero on a normalized
lower-tail degree. -/
theorem abelianEnvelopeTruncGE_X_isZero_of_decompositionLowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (lowerTail : ℕ) :
    CategoryTheory.Limits.IsZero
      ((TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
          cut
          complex).X
          (cut - 1 - (lowerTail : ℤ))) :=
  letI : ∀ degree : ℤ, complex.HasHomology degree :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainComplex_hasHomology_all complex
  (complex.truncGE'
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut))
    .isZero_extend_X'
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      (cut - 1 - (lowerTail : ℤ))
      (TraceAnalyticMotivicTStructure
        .truncGEEmbedding_r_eq_none_of_decompositionLowerTail
          cut
          lowerTail)

/-- The abelian-envelope upper projection component is zero on a normalized
lower-tail degree. -/
theorem abelianEnvelopeTruncGEProjectionMap_f_of_decompositionLowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGEProjectionMap
        cut
        complex).f
        (cut - 1 - (lowerTail : ℤ)) =
      0 :=
  letI : ∀ degree : ℤ, complex.HasHomology degree :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainComplex_hasHomology_all complex
  TraceAnalyticMotivicTStructure.truncGEProjectionMap_f_of_r_eq_none
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    (cut - 1 - (lowerTail : ℤ))
    (TraceAnalyticMotivicTStructure
      .truncGEEmbedding_r_eq_none_of_decompositionLowerTail
        cut
        lowerTail)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
