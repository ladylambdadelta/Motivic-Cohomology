import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.Map.Owner

/-!
# Normalized additive homotopy cone-to-upper map

This file sends the cochain-level cone-to-upper map through the additive
homotopy quotient and records its compatibility with the cone map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The additive homotopy cone-to-upper comparison map for the normalized lower
inclusion. -/
def additiveNormalizedConeComparisonMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeVertex
        cut
        complex ⟶
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTarget
        cut
        complex :=
  TraceAnalyticAdditiveHomotopyCategory.mapOf
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
      cut
      complex)

/-- The additive homotopy cone-to-upper comparison map is the homotopy image of
the concrete cochain-level comparison map. -/
theorem additiveNormalizedConeComparisonMap_eq_mapOf
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex =
      TraceAnalyticAdditiveHomotopyCategory.mapOf
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex) :=
  rfl

/-- The normalized additive cone map followed by the cone-to-upper comparison is
the named upper projection. -/
theorem additiveNormalizedLowerInclusionConeMap_comp_coneComparisonMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeMap
        cut
        complex ≫
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex =
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonProjection
        cut
        complex :=
  let lowerMap :
      TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE cut complex ⟶
        complex :=
    TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
      cut
      complex
  let coneMap :
      CochainComplex.mappingCone lowerMap ⟶
        TraceAnalyticMotivicTStructure.additiveTruncGE cut complex :=
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
      cut
      complex
  let inr_comp :
      CochainComplex.mappingCone.inr lowerMap ≫ coneMap =
        TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
          cut
          complex :=
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap_inr
      cut
      complex
  Eq.trans
    (Eq.symm
      (TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.map_comp
        (CochainComplex.mappingCone.inr lowerMap)
        coneMap))
    (congrArg
      TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.map
      inr_comp)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
