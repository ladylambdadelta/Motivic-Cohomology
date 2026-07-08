import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.ZeroCone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Transport.Comparison.CochainDecomposition.NullCone.Owner

/-!
# Zero-cone criterion for the transported normalized comparison

This file transfers the extracted zero-cone criterion to the transported
normalized short-complex comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the named additive cone-comparison cone object is zero, then the
transported normalized short-complex comparison is an isomorphism. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_eq_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hzero :
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex = 0) :
    IsIso
      (TraceAnalyticMotivicTStructure
        .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  TraceAnalyticMotivicTStructure
    .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_null
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
