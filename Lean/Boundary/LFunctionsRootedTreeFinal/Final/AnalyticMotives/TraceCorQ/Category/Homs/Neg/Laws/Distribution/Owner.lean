import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Distribution.Owner

/-!
# Negation distribution normal forms for typed trace-correspondence homs

This file owns longer-sum negation normalizers for typed hom classes.  Negation
is scalar multiplication by `-1`, so these are concrete wrappers around the
typed scalar distribution theorems.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Distribute typed hom negation over a left-associated three-summand sum. -/
theorem TraceCorQHom.neg_add_three_left
    {source target : TraceCorQObject}
    (first second third : TraceCorQHom source target) :
    TraceCorQHom.neg
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third) =
      TraceCorQHom.add
        (TraceCorQHom.neg first)
        (TraceCorQHom.add
          (TraceCorQHom.neg second)
          (TraceCorQHom.neg third)) :=
  TraceCorQHom.smul_add_three_left
    (-1)
    first
    second
    third

/-- Distribute typed hom negation over a right-associated three-summand sum. -/
theorem TraceCorQHom.neg_add_three_right
    {source target : TraceCorQObject}
    (first second third : TraceCorQHom source target) :
    TraceCorQHom.neg
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second third)) =
      TraceCorQHom.add
        (TraceCorQHom.neg first)
        (TraceCorQHom.add
          (TraceCorQHom.neg second)
          (TraceCorQHom.neg third)) :=
  TraceCorQHom.smul_add_three_right
    (-1)
    first
    second
    third

/-- Distribute typed hom negation over a fully left-associated four-summand sum. -/
theorem TraceCorQHom.neg_add_four_left
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.neg
      (TraceCorQHom.add
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        fourth) =
      TraceCorQHom.add
        (TraceCorQHom.neg first)
        (TraceCorQHom.add
          (TraceCorQHom.neg second)
          (TraceCorQHom.add
            (TraceCorQHom.neg third)
            (TraceCorQHom.neg fourth))) :=
  TraceCorQHom.smul_add_four_left
    (-1)
    first
    second
    third
    fourth

/-- Distribute typed hom negation over a fully right-associated four-summand sum. -/
theorem TraceCorQHom.neg_add_four_right
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.neg
      (TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth))) =
      TraceCorQHom.add
        (TraceCorQHom.neg first)
        (TraceCorQHom.add
          (TraceCorQHom.neg second)
          (TraceCorQHom.add
            (TraceCorQHom.neg third)
            (TraceCorQHom.neg fourth))) :=
  TraceCorQHom.smul_add_four_right
    (-1)
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary
