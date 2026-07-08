import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeVertex.Owner

/-!
# Normalized stable cone comparison target

This file names the upper-truncation target for the normalized stable
cone-to-upper comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The normalized stable cone comparison target is the upper stable
truncation at the upper boundary `cut`. -/
def stableNormalizedConeComparisonTarget
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticStableMotiveCategory :=
  TraceAnalyticMotivicTStructure.stableTruncGE cut complex

/-- The normalized stable cone comparison projection is the upper stable
projection map. -/
def stableNormalizedConeComparisonProjection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ⟶
      TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonTarget
        cut
        complex :=
  TraceAnalyticMotivicTStructure.stableTruncGEProjectionMap cut complex

/-- Projection formula for the normalized stable upper target. -/
theorem stableNormalizedConeComparisonTarget_eq_upper
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonTarget
        cut
        complex =
      TraceAnalyticMotivicTStructure.stableTruncGE cut complex :=
  rfl

/-- Projection formula for the normalized stable upper projection. -/
theorem stableNormalizedConeComparisonProjection_eq_upperProjection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonProjection
        cut
        complex =
      TraceAnalyticMotivicTStructure.stableTruncGEProjectionMap cut complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
