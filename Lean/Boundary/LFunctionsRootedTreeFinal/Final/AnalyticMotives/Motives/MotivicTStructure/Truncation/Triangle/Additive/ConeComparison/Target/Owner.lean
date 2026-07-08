import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.ConeVertex.Owner

/-!
# Additive cone comparison target

This file names the upper-truncation side that the additive lower-inclusion
cone vertex must be compared with before passing to the stable Verdier
quotient.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The upper-truncation homotopy object targeted by the additive cone
comparison. -/
def additiveLowerConeComparisonTarget
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotivicTStructure.homotopyTruncGE cut complex

/-- The homotopy upper projection map targeted by the additive cone
comparison. -/
def additiveLowerConeComparisonProjection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveHomotopyCategory.objectOf complex ⟶
      TraceAnalyticMotivicTStructure.additiveLowerConeComparisonTarget
        cut
        complex :=
  TraceAnalyticMotivicTStructure.homotopyTruncGEProjectionMap cut complex

/-- Projection formula for the additive upper-truncation comparison target. -/
theorem additiveLowerConeComparisonTarget_eq_upper
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveLowerConeComparisonTarget
        cut
        complex =
      TraceAnalyticMotivicTStructure.homotopyTruncGE cut complex :=
  rfl

/-- Projection formula for the additive upper projection comparison map. -/
theorem additiveLowerConeComparisonProjection_eq_upperProjection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveLowerConeComparisonProjection
        cut
        complex =
      TraceAnalyticMotivicTStructure.homotopyTruncGEProjectionMap cut complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
