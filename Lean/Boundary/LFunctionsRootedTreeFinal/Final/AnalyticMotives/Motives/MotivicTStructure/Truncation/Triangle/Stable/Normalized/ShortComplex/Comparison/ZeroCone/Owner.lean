import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Nullity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.NullCone.Owner

/-!
# Zero-cone criterion for the stable short-complex comparison

This file composes the concrete zero-cone criterion with the stable
short-complex comparison isomorphism theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the named additive cone-comparison cone object is zero, then the stable
short-complex comparison is an isomorphism. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_eq_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hzero :
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex = 0) :
    IsIso
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  TraceAnalyticMotivicTStructure
    .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_null
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonConeObject_null_of_eq_zero
          cut
          complex
          hzero)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
