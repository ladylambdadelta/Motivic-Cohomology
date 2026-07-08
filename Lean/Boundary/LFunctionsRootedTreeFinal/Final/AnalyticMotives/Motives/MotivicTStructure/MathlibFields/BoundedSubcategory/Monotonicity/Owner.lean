import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedSubcategory.Owner

/-!
# Monotonicity on bounded stable source predicates

The bounded stable source predicates are the ambient Mathlib-facing analytic
predicates pulled back along the bounded-source inclusion.  Their monotonicity
is therefore inherited directly from the ambient reindexed predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The bounded-source `LE` predicates are monotone in the displayed cut. -/
theorem mathlibLE_monotone :
    Monotone TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE :=
  fun lower upper cut_le object membership =>
    TraceAnalyticMotivicTStructure.mathlibLE_monotone
      cut_le
      membership

/-- The bounded-source `GE` predicates are antitone in the displayed cut. -/
theorem mathlibGE_antitone :
    Antitone TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE :=
  fun lower upper cut_le object membership =>
    TraceAnalyticMotivicTStructure.mathlibGE_antitone
      cut_le
      membership

/-- Mathlib `TStructure.LE_zero_le` field for the bounded-source predicates. -/
theorem mathlibLE_zero_le :
    TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 ≤
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 1 :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE_monotone
    (zero_le_one : (0 : ℤ) ≤ 1)

/-- Mathlib `TStructure.GE_one_le` field for the bounded-source predicates. -/
theorem mathlibGE_one_le :
    TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 ≤
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 0 :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE_antitone
    (zero_le_one : (0 : ℤ) ≤ 1)

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
