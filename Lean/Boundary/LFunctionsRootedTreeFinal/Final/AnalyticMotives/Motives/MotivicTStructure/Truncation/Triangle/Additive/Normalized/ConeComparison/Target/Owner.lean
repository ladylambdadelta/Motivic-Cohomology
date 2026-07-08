import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeVertex.Owner

/-!
# Normalized additive cone comparison target

This file names the upper-truncation target for the normalized additive
cone-to-upper comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The normalized additive cone comparison target is the upper homotopy
truncation at the upper boundary `cut`. -/
def additiveNormalizedConeComparisonTarget
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotivicTStructure.homotopyTruncGE cut complex

/-- The normalized additive cone comparison projection is the upper homotopy
projection map. -/
def additiveNormalizedConeComparisonProjection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveHomotopyCategory.objectOf complex ⟶
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTarget
        cut
        complex :=
  TraceAnalyticMotivicTStructure.homotopyTruncGEProjectionMap cut complex

/-- Projection formula for the normalized additive upper target. -/
theorem additiveNormalizedConeComparisonTarget_eq_upper
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTarget
        cut
        complex =
      TraceAnalyticMotivicTStructure.homotopyTruncGE cut complex :=
  rfl

/-- Projection formula for the normalized additive upper projection. -/
theorem additiveNormalizedConeComparisonProjection_eq_upperProjection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonProjection
        cut
        complex =
      TraceAnalyticMotivicTStructure.homotopyTruncGEProjectionMap cut complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
