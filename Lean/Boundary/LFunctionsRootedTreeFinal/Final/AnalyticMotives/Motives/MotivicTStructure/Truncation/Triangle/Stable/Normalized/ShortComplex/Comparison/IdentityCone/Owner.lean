import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.HomotopyEquiv.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.IsIso.Owner

/-!
# Identity-cone criterion for the stable short-complex comparison

This file composes the cochain-level identity-cone inversion theorem with the
stable short-complex comparison isomorphism criterion.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the normalized cone-to-upper cochain map is an isomorphism, then the
stable short-complex comparison from the normalized cone short complex to the
cochain truncation-decomposition short complex is an isomorphism. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_isIso_cochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    IsIso
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  TraceAnalyticMotivicTStructure
    .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_inverted
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonMap_inverted_of_isIso_cochainMap
          cut
          complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
