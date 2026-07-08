import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Full.Owner

/-!
# Scalar distribution normal forms for typed trace-correspondence homs

This file owns scalar-distribution wrappers for longer typed hom sums.  These
lemmas use the binary distribution law and additive reassociation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Distribute a scalar over a left-associated three-summand typed hom sum. -/
theorem TraceCorQHom.smul_add_three_left
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (first second third : TraceCorQHom source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third) =
      TraceCorQHom.add
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.add
          (TraceCorQHom.smul coefficient second)
          (TraceCorQHom.smul coefficient third)) :=
  Eq.trans
    (TraceCorQHom.smul_add
      coefficient
      (TraceCorQHom.add first second)
      third)
    (Eq.trans
      (congrArg
        (fun leftHom =>
          TraceCorQHom.add
            leftHom
            (TraceCorQHom.smul coefficient third))
        (TraceCorQHom.smul_add coefficient first second))
      (TraceCorQHom.add_assoc
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.smul coefficient second)
        (TraceCorQHom.smul coefficient third)))

/-- Distribute a scalar over a right-associated three-summand typed hom sum. -/
theorem TraceCorQHom.smul_add_three_right
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (first second third : TraceCorQHom source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second third)) =
      TraceCorQHom.add
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.add
          (TraceCorQHom.smul coefficient second)
          (TraceCorQHom.smul coefficient third)) :=
  Eq.trans
    (TraceCorQHom.smul_add
      coefficient
      first
      (TraceCorQHom.add second third))
    (congrArg
      (fun tail =>
        TraceCorQHom.add
          (TraceCorQHom.smul coefficient first)
          tail)
      (TraceCorQHom.smul_add coefficient second third))

/-- Distribute a scalar over a fully left-associated four-summand typed hom sum. -/
theorem TraceCorQHom.smul_add_four_left
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.add
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        fourth) =
      TraceCorQHom.add
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.add
          (TraceCorQHom.smul coefficient second)
          (TraceCorQHom.add
            (TraceCorQHom.smul coefficient third)
            (TraceCorQHom.smul coefficient fourth))) :=
  Eq.trans
    (TraceCorQHom.smul_add
      coefficient
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third)
      fourth)
    (Eq.trans
      (congrArg
        (fun headHom =>
          TraceCorQHom.add
            headHom
            (TraceCorQHom.smul coefficient fourth))
        (TraceCorQHom.smul_add_three_left
          coefficient
          first
          second
          third))
      (Eq.trans
        (TraceCorQHom.add_assoc
          (TraceCorQHom.smul coefficient first)
          (TraceCorQHom.add
            (TraceCorQHom.smul coefficient second)
            (TraceCorQHom.smul coefficient third))
          (TraceCorQHom.smul coefficient fourth))
        (congrArg
          (TraceCorQHom.add
            (TraceCorQHom.smul coefficient first))
          (TraceCorQHom.add_assoc
            (TraceCorQHom.smul coefficient second)
            (TraceCorQHom.smul coefficient third)
            (TraceCorQHom.smul coefficient fourth)))))

/-- Distribute a scalar over a fully right-associated four-summand typed hom sum. -/
theorem TraceCorQHom.smul_add_four_right
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth))) =
      TraceCorQHom.add
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.add
          (TraceCorQHom.smul coefficient second)
          (TraceCorQHom.add
            (TraceCorQHom.smul coefficient third)
            (TraceCorQHom.smul coefficient fourth))) :=
  Eq.trans
    (TraceCorQHom.smul_add
      coefficient
      first
      (TraceCorQHom.add
        second
        (TraceCorQHom.add third fourth)))
    (congrArg
      (fun tail =>
        TraceCorQHom.add
          (TraceCorQHom.smul coefficient first)
          tail)
      (TraceCorQHom.smul_add_three_right
        coefficient
        second
        third
        fourth))

end AnalyticMotives
end LFunctions
end Boundary
