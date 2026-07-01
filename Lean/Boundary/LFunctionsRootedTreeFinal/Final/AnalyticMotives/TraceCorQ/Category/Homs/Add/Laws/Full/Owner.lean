import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Owner

/-!
# Full additive reassociation for typed trace-correspondence homs

This file owns four-summand additive normalization for typed hom classes.  The
normal form is the fully right-associated sum.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Normalize the fully left-associated four-summand typed hom sum. -/
theorem TraceCorQHom.add_assoc_four_left
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third)
      fourth =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth)) :=
  Eq.trans
    (TraceCorQHom.add_assoc
      (TraceCorQHom.add first second)
      third
      fourth)
    (TraceCorQHom.add_assoc
      first
      second
      (TraceCorQHom.add third fourth))

/-- Normalize the four-summand typed hom sum with the middle pair grouped first. -/
theorem TraceCorQHom.add_assoc_four_middle_left
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second third))
      fourth =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth)) :=
  Eq.trans
    (TraceCorQHom.add_assoc
      first
      (TraceCorQHom.add second third)
      fourth)
    (congrArg
      (fun tail =>
        TraceCorQHom.add first tail)
      (TraceCorQHom.add_assoc
        second
        third
        fourth))

/-- Normalize the four-summand typed hom sum split as two binary sums. -/
theorem TraceCorQHom.add_assoc_four_binary
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.add first second)
      (TraceCorQHom.add third fourth) =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth)) :=
  TraceCorQHom.add_assoc
    first
    second
    (TraceCorQHom.add third fourth)

/-- Normalize the four-summand typed hom sum whose right tail is left-associated. -/
theorem TraceCorQHom.add_assoc_four_middle_right
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.add
      first
      (TraceCorQHom.add
        (TraceCorQHom.add second third)
        fourth) =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth)) :=
  congrArg
    (fun tail =>
      TraceCorQHom.add first tail)
    (TraceCorQHom.add_assoc
      second
      third
      fourth)

/-- The fully right-associated four-summand typed hom sum is already normal. -/
theorem TraceCorQHom.add_assoc_four_right
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.add
      first
      (TraceCorQHom.add
        second
        (TraceCorQHom.add third fourth)) =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth)) :=
  Eq.refl
    (TraceCorQHom.add
      first
      (TraceCorQHom.add
        second
        (TraceCorQHom.add third fourth)))

end AnalyticMotives
end LFunctions
end Boundary
