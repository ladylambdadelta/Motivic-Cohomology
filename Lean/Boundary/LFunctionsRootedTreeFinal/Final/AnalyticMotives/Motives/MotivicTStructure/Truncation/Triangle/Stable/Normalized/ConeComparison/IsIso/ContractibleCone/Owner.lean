import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Contractible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.IsIso.Owner

/-!
# Contractible-cone isomorphism criterion for the stable cone comparison

This file composes the concrete contracting-homotopy criterion with the
Verdier localization criterion for the stable cone-to-upper comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- A contracting homotopy of the concrete mapping cone of the normalized
cone-to-upper cochain map makes the stable cone comparison an isomorphism. -/
theorem stableNormalizedConeComparisonMap_isIso_of_contractibleCone
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (contractible :
      Nonempty
        (Homotopy
          (𝟙
            (CochainComplex.mappingCone
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonCochainMap cut complex)))
          0)) :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap_isIso_of_inverted
    cut
    complex
    (TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonMap_inverted_of_contractibleCone
        cut
        complex
        contractible)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
