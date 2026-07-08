import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.IsoClosure.Owner

/-!
# Mathlib-facing reindexed analytic motivic predicates

Mathlib's `TStructure` shift convention is contravariant in the displayed cut:
from `a + n' = n`, an object in `LE n` shifts to an object in `LE n'`.
The concrete analytic representative degree convention shifts degrees by
addition.  The Mathlib-facing predicates therefore use the opposite cut and
swap the concrete analytic coaisle/aisle roles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Mathlib-facing analytic `LE` predicate at cut `cut`.

This is the iso-closed concrete analytic coaisle at the opposite cut. -/
abbrev TraceAnalyticMotivicTStructure.mathlibLE
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource → Prop :=
  TraceAnalyticMotivicTStructure.coaisleGEIsoClosed (-cut)

/-- Mathlib-facing analytic `GE` predicate at cut `cut`.

This is the iso-closed concrete analytic aisle at the opposite cut. -/
abbrev TraceAnalyticMotivicTStructure.mathlibGE
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource → Prop :=
  TraceAnalyticMotivicTStructure.aisleLEIsoClosed (-cut)

/-- The Mathlib-facing `LE` predicate is closed under isomorphisms. -/
def TraceAnalyticMotivicTStructure.mathlibLE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticMotivicTStructure.mathlibLE cut) :=
  TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_closedUnderIsomorphisms
    (-cut)

/-- The Mathlib-facing `GE` predicate is closed under isomorphisms. -/
def TraceAnalyticMotivicTStructure.mathlibGE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticMotivicTStructure.mathlibGE cut) :=
  TraceAnalyticMotivicTStructure.aisleLEIsoClosed_closedUnderIsomorphisms
    (-cut)

/-- Mathlib-facing analytic `LE` predicates are monotone in the displayed cut. -/
theorem TraceAnalyticMotivicTStructure.mathlibLE_monotone :
    Monotone TraceAnalyticMotivicTStructure.mathlibLE :=
  fun lower upper cut_le =>
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_antitone
      (neg_le_neg cut_le)

/-- Mathlib-facing analytic `GE` predicates are antitone in the displayed cut. -/
theorem TraceAnalyticMotivicTStructure.mathlibGE_antitone :
    Antitone TraceAnalyticMotivicTStructure.mathlibGE :=
  fun lower upper cut_le =>
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed_monotone
      (neg_le_neg cut_le)

/-- Mathlib `TStructure.LE_zero_le` field for the reindexed analytic
predicates. -/
theorem TraceAnalyticMotivicTStructure.mathlibLE_zero_le :
    TraceAnalyticMotivicTStructure.mathlibLE 0 ≤
      TraceAnalyticMotivicTStructure.mathlibLE 1 :=
  TraceAnalyticMotivicTStructure.mathlibLE_monotone
    (zero_le_one : (0 : ℤ) ≤ 1)

/-- Mathlib `TStructure.GE_one_le` field for the reindexed analytic
predicates. -/
theorem TraceAnalyticMotivicTStructure.mathlibGE_one_le :
    TraceAnalyticMotivicTStructure.mathlibGE 1 ≤
      TraceAnalyticMotivicTStructure.mathlibGE 0 :=
  TraceAnalyticMotivicTStructure.mathlibGE_antitone
    (zero_le_one : (0 : ℤ) ≤ 1)

end AnalyticMotives
end LFunctions
end Boundary
