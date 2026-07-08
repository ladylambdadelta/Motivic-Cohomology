import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.YonedaComplex.Reflection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.Map.Owner

/-!
# Yoneda reflection for the normalized cone comparison

This file specializes cochain-level Yoneda isomorphism reflection to the
normalized cone-to-upper comparison map.  The remaining exactness calculation
can therefore be carried out in the abelian-envelope cochain category and
reflected back to the concrete additive cochain map through this theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the represented abelian-envelope cochain map of the normalized
cone-to-upper comparison is an isomorphism, then the concrete additive
cone-to-upper comparison is an isomorphism. -/
theorem additiveNormalizedConeComparisonCochainMap_isIso_of_yoneda_isIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainMap
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparisonCochainMap cut complex))] :
    IsIso
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonCochainMap cut complex) :=
  TraceAnalyticAdditiveAbelianEnvelope
    .isIso_of_yonedaCochainMap_isIso
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonCochainMap cut complex)

/-- The normalized cone-to-upper comparison is an isomorphism exactly when its
represented abelian-envelope cochain map is an isomorphism. -/
theorem additiveNormalizedConeComparisonCochainMap_yoneda_isIso_iff
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    IsIso
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainMap
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex)) ↔
      IsIso
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparisonCochainMap cut complex) :=
  TraceAnalyticAdditiveAbelianEnvelope
    .yonedaCochainMap_isIso_iff
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonCochainMap cut complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
