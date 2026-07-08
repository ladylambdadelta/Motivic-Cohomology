import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.HomotopyMap.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.Target.Owner

/-!
# Normalized stable cone-to-upper map

This file sends the additive homotopy cone-to-upper comparison map through the
stable Verdier quotient and records its compatibility with the stable cone map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The stable cone-to-upper comparison map for the normalized lower
inclusion. -/
def stableNormalizedConeComparisonMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeVertex
        cut
        complex ⟶
      TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonTarget
        cut
        complex :=
  TraceAnalyticStableMotiveCategory.mapOf
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
      cut
      complex)

/-- The stable cone-to-upper comparison map is the Verdier image of the
additive homotopy cone-to-upper comparison map. -/
theorem stableNormalizedConeComparisonMap_eq_mapOf
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex =
      TraceAnalyticStableMotiveCategory.mapOf
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
          cut
          complex) :=
  rfl

/-- The normalized stable cone map followed by the stable cone-to-upper
comparison is the named stable upper projection. -/
theorem stableNormalizedLowerInclusionConeMap_comp_coneComparisonMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeMap
        cut
        complex ≫
      TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex =
      TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonProjection
        cut
        complex :=
  let additiveConeMap :
      TraceAnalyticAdditiveHomotopyCategory.objectOf complex ⟶
        TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeVertex
          cut
          complex :=
    TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeMap
      cut
      complex
  let additiveComparisonMap :
      TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeVertex
          cut
          complex ⟶
        TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTarget
          cut
          complex :=
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
      cut
      complex
  let additive_comp :
      additiveConeMap ≫ additiveComparisonMap =
        TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonProjection
          cut
          complex :=
    TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeMap_comp_coneComparisonMap
      cut
      complex
  Eq.trans
    (Eq.symm
      (TraceAnalyticStableMotiveCategory.quotientFunctor.map_comp
        additiveConeMap
        additiveComparisonMap))
    (congrArg
      TraceAnalyticStableMotiveCategory.quotientFunctor.map
      additive_comp)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
