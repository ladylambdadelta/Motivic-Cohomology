import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Monotone.Owner

/-!
# Mathlib t-structure monotonicity fields

This file proves the adjacent-cut monotonicity fields required by Mathlib's
`CategoryTheory.Triangulated.TStructure` record for the concrete analytic
aisle and coaisle predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic aisle predicates are monotone in the cut. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_monotone :
    Monotone TraceAnalyticMotivicTStructure.aisleLE :=
  fun lower upper cut_le object membership =>
    TraceAnalyticMotivicTStructure.aisleLE_mono
      cut_le
      membership

/-- The analytic coaisle predicates are antitone in the cut. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_antitone :
    Antitone TraceAnalyticMotivicTStructure.coaisleGE :=
  fun lower upper cut_le object membership =>
    TraceAnalyticMotivicTStructure.coaisleGE_mono
      cut_le
      membership

/-- Mathlib `TStructure.LE_zero_le` field for the concrete analytic aisle
predicates. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_zero_le :
    TraceAnalyticMotivicTStructure.aisleLE 0 ≤
      TraceAnalyticMotivicTStructure.aisleLE 1 :=
  fun object membership =>
    TraceAnalyticMotivicTStructure.aisleLE_mono
      (zero_le_one : (0 : ℤ) ≤ 1)
      membership

/-- Mathlib `TStructure.GE_one_le` field for the concrete analytic coaisle
predicates. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_one_le :
    TraceAnalyticMotivicTStructure.coaisleGE 1 ≤
      TraceAnalyticMotivicTStructure.coaisleGE 0 :=
  fun object membership =>
    TraceAnalyticMotivicTStructure.coaisleGE_mono
      (zero_le_one : (0 : ℤ) ≤ 1)
      membership

end AnalyticMotives
end LFunctions
end Boundary
