import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Owner

/-!
# Full additive reassociation for quotient trace correspondences

This file owns four-summand additive normalization for quotient
trace-correspondence classes.  The normal form is the fully right-associated
sum.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Normalize the fully left-associated four-summand quotient sum. -/
theorem TraceCorQQuotient.add_assoc_four_left
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third)
      fourth =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth)) :=
  Eq.trans
    (TraceCorQQuotient.add_assoc
      (TraceCorQQuotient.add first second)
      third
      fourth)
    (TraceCorQQuotient.add_assoc
      first
      second
      (TraceCorQQuotient.add third fourth))

/-- Normalize the four-summand quotient sum with the middle pair grouped first. -/
theorem TraceCorQQuotient.add_assoc_four_middle_left
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add second third))
      fourth =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth)) :=
  Eq.trans
    (TraceCorQQuotient.add_assoc
      first
      (TraceCorQQuotient.add second third)
      fourth)
    (congrArg
      (fun tail =>
        TraceCorQQuotient.add first tail)
      (TraceCorQQuotient.add_assoc
        second
        third
        fourth))

/-- Normalize the four-summand quotient sum split as two binary sums. -/
theorem TraceCorQQuotient.add_assoc_four_binary
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.add first second)
      (TraceCorQQuotient.add third fourth) =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth)) :=
  TraceCorQQuotient.add_assoc
    first
    second
    (TraceCorQQuotient.add third fourth)

/-- Normalize the four-summand quotient sum whose right tail is left-associated. -/
theorem TraceCorQQuotient.add_assoc_four_middle_right
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.add
      first
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add second third)
        fourth) =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth)) :=
  congrArg
    (fun tail =>
      TraceCorQQuotient.add first tail)
    (TraceCorQQuotient.add_assoc
      second
      third
      fourth)

/-- The fully right-associated four-summand quotient sum is already normal. -/
theorem TraceCorQQuotient.add_assoc_four_right
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.add
      first
      (TraceCorQQuotient.add
        second
        (TraceCorQQuotient.add third fourth)) =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth)) :=
  Eq.refl
    (TraceCorQQuotient.add
      first
      (TraceCorQQuotient.add
        second
        (TraceCorQQuotient.add third fourth)))

end AnalyticMotives
end LFunctions
end Boundary
