import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.ConeVertex.Owner

/-!
# Stable cone comparison target

This file names the upper-truncation side that the stable lower-inclusion cone
vertex must be compared with.  It does not assert the comparison isomorphism;
it fixes the concrete target object and map supplied by the truncation
construction.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The upper-truncation object targeted by the stable cone comparison. -/
def stableLowerConeComparisonTarget
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticStableMotiveCategory :=
  TraceAnalyticMotivicTStructure.stableTruncGE cut complex

/-- The stable upper projection map targeted by the stable cone comparison. -/
def stableLowerConeComparisonProjection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ⟶
      TraceAnalyticMotivicTStructure.stableLowerConeComparisonTarget
        cut
        complex :=
  TraceAnalyticMotivicTStructure.stableTruncGEProjectionMap cut complex

/-- Projection formula for the upper-truncation comparison target. -/
theorem stableLowerConeComparisonTarget_eq_upper
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableLowerConeComparisonTarget
        cut
        complex =
      TraceAnalyticMotivicTStructure.stableTruncGE cut complex :=
  rfl

/-- Projection formula for the stable upper projection comparison map. -/
theorem stableLowerConeComparisonProjection_eq_upperProjection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableLowerConeComparisonProjection
        cut
        complex =
      TraceAnalyticMotivicTStructure.stableTruncGEProjectionMap cut complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
