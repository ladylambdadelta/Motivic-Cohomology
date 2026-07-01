import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Associativity.FormalSums.Owner

/-!
# Fourfold associativity edges for quotient trace-correspondence composition

This file owns the elementary reassociation edges between the five
parenthesizations of a fourfold quotient composite.  The full normalization
file composes these edges into right-associated normal forms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Move the outer three factors of a fully left-associated composite. -/
theorem TraceCorQQuotient.comp_assoc_four_left_outer_edge
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.comp first second)
        third)
      fourth =
      TraceCorQQuotient.comp
        (TraceCorQQuotient.comp first second)
        (TraceCorQQuotient.comp third fourth) :=
  TraceCorQQuotient.comp_assoc
    (TraceCorQQuotient.comp first second)
    third
    fourth

/-- Move the final three factors inside a left head. -/
theorem TraceCorQQuotient.comp_assoc_four_left_inner_edge
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp first second)
      (TraceCorQQuotient.comp third fourth) =
      TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp
          second
          (TraceCorQQuotient.comp third fourth)) :=
  TraceCorQQuotient.comp_assoc
    first
    second
    (TraceCorQQuotient.comp third fourth)

/-- Move the outer factors of a composite whose middle pair was first. -/
theorem TraceCorQQuotient.comp_assoc_four_middle_left_outer_edge
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp second third))
      fourth =
      TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp
          (TraceCorQQuotient.comp second third)
          fourth) :=
  TraceCorQQuotient.comp_assoc
    first
    (TraceCorQQuotient.comp second third)
    fourth

/-- Reassociate the right tail of a fourfold composite. -/
theorem TraceCorQQuotient.comp_assoc_four_tail_edge
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      first
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.comp second third)
        fourth) =
      TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp
          second
          (TraceCorQQuotient.comp third fourth)) :=
  congrArg
    (fun tail =>
      TraceCorQQuotient.comp first tail)
    (TraceCorQQuotient.comp_assoc
      second
      third
      fourth)

end AnalyticMotives
end LFunctions
end Boundary
