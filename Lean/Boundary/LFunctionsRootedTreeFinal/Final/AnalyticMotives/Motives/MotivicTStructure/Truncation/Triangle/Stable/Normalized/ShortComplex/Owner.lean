import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeVertex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.Projections.Owner

/-!
# Normalized stable truncation short complex

The normalized lower-inclusion triangle remains distinguished after Verdier
localization.  This file extracts the associated short complex in the stable
analytic motive category, making the stable composite-zero field explicit.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The short complex attached to the normalized stable lower-inclusion
distinguished triangle. -/
def stableNormalizedLowerInclusionShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    ShortComplex TraceAnalyticStableMotiveCategory :=
  shortComplexOfDistTriangle
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle_distinguished
      cut
      complex)

/-- The first object of the normalized stable short complex is the stable image
of the paired lower truncation. -/
theorem stableNormalizedLowerInclusionShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
      cut
      complex).X₁ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex)) :=
  rfl

/-- The second object of the normalized stable short complex is the stable image
of the original complex. -/
theorem stableNormalizedLowerInclusionShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
      cut
      complex).X₂ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  rfl

/-- The third object of the normalized stable short complex is the named stable
cone vertex. -/
theorem stableNormalizedLowerInclusionShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
      cut
      complex).X₃ =
      TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeVertex
        cut
        complex :=
  rfl

/-- The first map of the normalized stable short complex is the Verdier image
of the paired lower truncation inclusion. -/
theorem stableNormalizedLowerInclusionShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
      cut
      complex).f =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticAdditiveHomotopyCategory.mapOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
            cut
            complex)) :=
  rfl

/-- The second map of the normalized stable short complex is the stable cone map
of the normalized lower-inclusion triangle. -/
theorem stableNormalizedLowerInclusionShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
      cut
      complex).g =
      TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeMap
        cut
        complex :=
  rfl

/-- The normalized stable lower-inclusion map followed by its stable cone map
is zero. -/
theorem stableNormalizedLowerInclusionShortComplex_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
      cut
      complex).f ≫
        (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
          cut
          complex).g =
      0 :=
  (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
    cut
    complex).zero

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
