import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Full.Owner

/-!
# Longer additive distribution for quotient composition

This file owns normal forms for composing three- and four-summand quotient sums
on either side.  The target normal form is fully right-associated.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compose a left-associated three-summand quotient source sum on the right. -/
theorem TraceCorQQuotient.add_add_comp
    (first second third tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third)
      tail =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp first tail)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp second tail)
          (TraceCorQQuotient.comp third tail)) :=
  Eq.trans
    (TraceCorQQuotient.add_comp
      (TraceCorQQuotient.add first second)
      third
      tail)
    (Eq.trans
      (congrArg
        (fun head =>
          TraceCorQQuotient.add head (TraceCorQQuotient.comp third tail))
        (TraceCorQQuotient.add_comp first second tail))
      (TraceCorQQuotient.add_assoc
        (TraceCorQQuotient.comp first tail)
        (TraceCorQQuotient.comp second tail)
        (TraceCorQQuotient.comp third tail)))

/-- Compose a right-associated three-summand quotient source sum on the right. -/
theorem TraceCorQQuotient.add_add_comp_right
    (first second third tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add second third))
      tail =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp first tail)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp second tail)
          (TraceCorQQuotient.comp third tail)) :=
  Eq.trans
    (TraceCorQQuotient.add_comp
      first
      (TraceCorQQuotient.add second third)
      tail)
    (congrArg
      (TraceCorQQuotient.add (TraceCorQQuotient.comp first tail))
      (TraceCorQQuotient.add_comp second third tail))

/-- Compose a fully left-associated four-summand quotient source sum on the right. -/
theorem TraceCorQQuotient.add_add_add_comp
    (first second third fourth tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)
        fourth)
      tail =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp first tail)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp second tail)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp third tail)
            (TraceCorQQuotient.comp fourth tail))) :=
  Eq.trans
    (TraceCorQQuotient.add_comp
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third)
      fourth
      tail)
    (Eq.trans
      (congrArg
        (fun head =>
          TraceCorQQuotient.add head (TraceCorQQuotient.comp fourth tail))
        (TraceCorQQuotient.add_add_comp first second third tail))
      (TraceCorQQuotient.add_assoc_four_left
        (TraceCorQQuotient.comp first tail)
        (TraceCorQQuotient.comp second tail)
        (TraceCorQQuotient.comp third tail)
        (TraceCorQQuotient.comp fourth tail)))

/-- Compose a fully right-associated four-summand quotient source sum on the right. -/
theorem TraceCorQQuotient.add_add_add_comp_right
    (first second third fourth tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth)))
      tail =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp first tail)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp second tail)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp third tail)
            (TraceCorQQuotient.comp fourth tail))) :=
  Eq.trans
    (TraceCorQQuotient.add_comp
      first
      (TraceCorQQuotient.add
        second
        (TraceCorQQuotient.add third fourth))
      tail)
    (congrArg
      (TraceCorQQuotient.add (TraceCorQQuotient.comp first tail))
      (TraceCorQQuotient.add_add_comp_right second third fourth tail))

/-- Compose on a left-associated three-summand quotient target sum. -/
theorem TraceCorQQuotient.comp_add_add
    (head first second third : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      head
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp head first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp head second)
          (TraceCorQQuotient.comp head third)) :=
  Eq.trans
    (TraceCorQQuotient.comp_add
      head
      (TraceCorQQuotient.add first second)
      third)
    (Eq.trans
      (congrArg
        (fun headClass =>
          TraceCorQQuotient.add headClass (TraceCorQQuotient.comp head third))
        (TraceCorQQuotient.comp_add head first second))
      (TraceCorQQuotient.add_assoc
        (TraceCorQQuotient.comp head first)
        (TraceCorQQuotient.comp head second)
        (TraceCorQQuotient.comp head third)))

/-- Compose on a right-associated three-summand quotient target sum. -/
theorem TraceCorQQuotient.comp_add_add_right
    (head first second third : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      head
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add second third)) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp head first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp head second)
          (TraceCorQQuotient.comp head third)) :=
  Eq.trans
    (TraceCorQQuotient.comp_add
      head
      first
      (TraceCorQQuotient.add second third))
    (congrArg
      (TraceCorQQuotient.add (TraceCorQQuotient.comp head first))
      (TraceCorQQuotient.comp_add head second third))

/-- Compose on a fully left-associated four-summand quotient target sum. -/
theorem TraceCorQQuotient.comp_add_add_add
    (head first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      head
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)
        fourth) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp head first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp head second)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp head third)
            (TraceCorQQuotient.comp head fourth))) :=
  Eq.trans
    (TraceCorQQuotient.comp_add
      head
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third)
      fourth)
    (Eq.trans
      (congrArg
        (fun headClass =>
          TraceCorQQuotient.add headClass (TraceCorQQuotient.comp head fourth))
        (TraceCorQQuotient.comp_add_add head first second third))
      (TraceCorQQuotient.add_assoc_four_left
        (TraceCorQQuotient.comp head first)
        (TraceCorQQuotient.comp head second)
        (TraceCorQQuotient.comp head third)
        (TraceCorQQuotient.comp head fourth)))

/-- Compose on a fully right-associated four-summand quotient target sum. -/
theorem TraceCorQQuotient.comp_add_add_add_right
    (head first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      head
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth))) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp head first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp head second)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp head third)
            (TraceCorQQuotient.comp head fourth))) :=
  Eq.trans
    (TraceCorQQuotient.comp_add
      head
      first
      (TraceCorQQuotient.add
        second
        (TraceCorQQuotient.add third fourth)))
    (congrArg
      (TraceCorQQuotient.add (TraceCorQQuotient.comp head first))
      (TraceCorQQuotient.comp_add_add_right head second third fourth))

end AnalyticMotives
end LFunctions
end Boundary
