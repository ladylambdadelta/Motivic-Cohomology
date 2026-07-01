import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Associativity.Full.Edges.Owner

/-!
# Full associativity normalization for quotient trace-correspondence composition

This file owns fourfold reassociation wrappers for quotient composition.  The
normal form is the fully right-associated composite.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Normalize the fully left-associated fourfold quotient composite. -/
theorem TraceCorQQuotient.comp_assoc_four_left
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.comp first second)
        third)
      fourth =
      TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp
          second
          (TraceCorQQuotient.comp third fourth)) :=
  Eq.trans
    (TraceCorQQuotient.comp_assoc_four_left_outer_edge
      first
      second
      third
      fourth)
    (TraceCorQQuotient.comp_assoc_four_left_inner_edge
      first
      second
      third
      fourth)

/-- Normalize the quotient composite with the middle pair associated first. -/
theorem TraceCorQQuotient.comp_assoc_four_middle_left
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp second third))
      fourth =
      TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp
          second
          (TraceCorQQuotient.comp third fourth)) :=
  Eq.trans
    (TraceCorQQuotient.comp_assoc_four_middle_left_outer_edge
      first
      second
      third
      fourth)
    (TraceCorQQuotient.comp_assoc_four_tail_edge
      first
      second
      third
      fourth)

/-- Normalize the quotient composite split as two binary composites. -/
theorem TraceCorQQuotient.comp_assoc_four_binary
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp first second)
      (TraceCorQQuotient.comp third fourth) =
      TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp
          second
          (TraceCorQQuotient.comp third fourth)) :=
  TraceCorQQuotient.comp_assoc_four_left_inner_edge
    first
    second
    third
    fourth

/-- Normalize the quotient composite whose right tail is left-associated. -/
theorem TraceCorQQuotient.comp_assoc_four_middle_right
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
  TraceCorQQuotient.comp_assoc_four_tail_edge
    first
    second
    third
    fourth

/-- The right-associated fourfold quotient composite is already normal. -/
theorem TraceCorQQuotient.comp_assoc_four_right
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      first
      (TraceCorQQuotient.comp
        second
        (TraceCorQQuotient.comp third fourth)) =
      TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp
          second
          (TraceCorQQuotient.comp third fourth)) :=
  Eq.refl
    (TraceCorQQuotient.comp
      first
      (TraceCorQQuotient.comp
        second
        (TraceCorQQuotient.comp third fourth)))

end AnalyticMotives
end LFunctions
end Boundary
