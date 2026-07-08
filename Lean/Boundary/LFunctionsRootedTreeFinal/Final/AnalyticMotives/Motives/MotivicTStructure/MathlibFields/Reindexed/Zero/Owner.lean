import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Zero.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Reindexed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.IsoClosure.Representatives.Owner

/-!
# Zero representatives for Mathlib-facing analytic motivic predicates

This file records the canonical shifted zero bounded representative used as an
endpoint for later truncation triangles.  At Mathlib cut `cut`, the
representative degree is the opposite cut `-cut`, matching the reindexed
`LE`/`GE` predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The shifted stable zero representative at the Mathlib-facing cut `cut`. -/
def TraceAnalyticMotivicTStructure.mathlibZeroRepresentative
    (bound : Nat)
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
    (TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy bound)
    (-cut)

/-- The Mathlib-facing zero representative is its underlying shifted stable
zero bounded object. -/
theorem TraceAnalyticMotivicTStructure.mathlibZeroRepresentative_eq
    (bound : Nat)
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.mathlibZeroRepresentative bound cut =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        (TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy bound)
        (-cut) :=
  rfl

/-- The shifted zero representative lies in the Mathlib-facing `LE` predicate
at its cut. -/
theorem TraceAnalyticMotivicTStructure.mathlibLE_zeroRepresentative
    (bound : Nat)
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.mathlibLE
      cut
      (TraceAnalyticMotivicTStructure.mathlibZeroRepresentative bound cut) :=
  TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_of_shiftedBounded_self
    (TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy bound)
    (-cut)

/-- The shifted zero representative lies in the Mathlib-facing `GE` predicate
at its cut. -/
theorem TraceAnalyticMotivicTStructure.mathlibGE_zeroRepresentative
    (bound : Nat)
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.mathlibGE
      cut
      (TraceAnalyticMotivicTStructure.mathlibZeroRepresentative bound cut) :=
  TraceAnalyticMotivicTStructure.aisleLEIsoClosed_of_shiftedBounded_self
    (TraceAnalyticMotiveComparison.sourceZeroComplexWeightBoundedBy bound)
    (-cut)

/-- The shifted zero representative belongs to both Mathlib-facing predicates
at its cut. -/
theorem TraceAnalyticMotivicTStructure.mathlibZeroRepresentative_mem_LE_and_GE
    (bound : Nat)
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.mathlibLE
        cut
        (TraceAnalyticMotivicTStructure.mathlibZeroRepresentative bound cut) ∧
      TraceAnalyticMotivicTStructure.mathlibGE
        cut
        (TraceAnalyticMotivicTStructure.mathlibZeroRepresentative bound cut) :=
  And.intro
    (TraceAnalyticMotivicTStructure.mathlibLE_zeroRepresentative bound cut)
    (TraceAnalyticMotivicTStructure.mathlibGE_zeroRepresentative bound cut)

end AnalyticMotives
end LFunctions
end Boundary
