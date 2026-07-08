import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.HomotopyEquiv.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.IsIso.Owner

/-!
# Identity-cone criterion for the normalized stable cone comparison

This file composes the cochain-level identity-cone comparison with the Verdier
localization criterion for the stable cone-to-upper comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the normalized cone-to-upper cochain map is an isomorphism, then the
stable cone-to-upper comparison is an isomorphism. -/
theorem stableNormalizedConeComparisonMap_isIso_of_isIso_cochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap_isIso_of_inverted
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
