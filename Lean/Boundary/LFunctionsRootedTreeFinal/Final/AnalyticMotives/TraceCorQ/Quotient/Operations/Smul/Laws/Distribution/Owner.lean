import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Full.Owner

/-!
# Scalar distribution normal forms for quotient trace correspondences

This file owns scalar-distribution wrappers for longer quotient sums.  These
lemmas use the already-proved binary distribution law and additive
reassociation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Distribute a scalar over a left-associated three-summand quotient sum. -/
theorem TraceCorQQuotient.smul_add_three_left
    (coefficient : Rat)
    (first second third : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.smul coefficient second)
          (TraceCorQQuotient.smul coefficient third)) :=
  Eq.trans
    (TraceCorQQuotient.smul_add
      coefficient
      (TraceCorQQuotient.add first second)
      third)
    (Eq.trans
      (congrArg
        (fun leftClass =>
          TraceCorQQuotient.add
            leftClass
            (TraceCorQQuotient.smul coefficient third))
        (TraceCorQQuotient.smul_add coefficient first second))
      (TraceCorQQuotient.add_assoc
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.smul coefficient second)
        (TraceCorQQuotient.smul coefficient third)))

/-- Distribute a scalar over a right-associated three-summand quotient sum. -/
theorem TraceCorQQuotient.smul_add_three_right
    (coefficient : Rat)
    (first second third : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add second third)) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.smul coefficient second)
          (TraceCorQQuotient.smul coefficient third)) :=
  Eq.trans
    (TraceCorQQuotient.smul_add
      coefficient
      first
      (TraceCorQQuotient.add second third))
    (congrArg
      (fun tail =>
        TraceCorQQuotient.add
          (TraceCorQQuotient.smul coefficient first)
          tail)
      (TraceCorQQuotient.smul_add coefficient second third))

/-- Distribute a scalar over a fully left-associated four-summand quotient sum. -/
theorem TraceCorQQuotient.smul_add_four_left
    (coefficient : Rat)
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)
        fourth) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.smul coefficient second)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.smul coefficient third)
            (TraceCorQQuotient.smul coefficient fourth))) :=
  Eq.trans
    (TraceCorQQuotient.smul_add
      coefficient
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third)
      fourth)
    (Eq.trans
      (congrArg
        (fun headClass =>
          TraceCorQQuotient.add
            headClass
            (TraceCorQQuotient.smul coefficient fourth))
        (TraceCorQQuotient.smul_add_three_left
          coefficient
          first
          second
          third))
      (TraceCorQQuotient.add_assoc_four_left
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.smul coefficient second)
        (TraceCorQQuotient.smul coefficient third)
        (TraceCorQQuotient.smul coefficient fourth)))

/-- Distribute a scalar over a fully right-associated four-summand quotient sum. -/
theorem TraceCorQQuotient.smul_add_four_right
    (coefficient : Rat)
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth))) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.smul coefficient second)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.smul coefficient third)
            (TraceCorQQuotient.smul coefficient fourth))) :=
  Eq.trans
    (TraceCorQQuotient.smul_add
      coefficient
      first
      (TraceCorQQuotient.add
        second
        (TraceCorQQuotient.add third fourth)))
    (congrArg
      (fun tail =>
        TraceCorQQuotient.add
          (TraceCorQQuotient.smul coefficient first)
          tail)
      (TraceCorQQuotient.smul_add_three_right
        coefficient
        second
        third
        fourth))

end AnalyticMotives
end LFunctions
end Boundary
