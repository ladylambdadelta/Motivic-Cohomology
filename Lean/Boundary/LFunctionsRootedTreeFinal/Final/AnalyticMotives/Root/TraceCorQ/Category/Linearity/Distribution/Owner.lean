import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Distribution.Owner

/-!
# Public additive distribution for TraceCorQ composition

This file exposes three- and four-summand additive distribution normal forms
for typed trace-correspondence composition through the public analytic-motives
root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: compose a left-associated three-summand source sum on the right. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_add_comp
    {source middle target : TraceCorQObject}
    (first second third : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third)
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp first tail)
        (TraceCorQHom.add
          (TraceCorQHom.comp second tail)
          (TraceCorQHom.comp third tail)) :=
  TraceCorQHom.add_add_comp
    first
    second
    third
    tail

/-- Public wrapper: compose a right-associated three-summand source sum on the right. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_add_comp_right
    {source middle target : TraceCorQObject}
    (first second third : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second third))
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp first tail)
        (TraceCorQHom.add
          (TraceCorQHom.comp second tail)
          (TraceCorQHom.comp third tail)) :=
  TraceCorQHom.add_add_comp_right
    first
    second
    third
    tail

/-- Public wrapper: compose a left-associated four-summand source sum on the right. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_add_add_comp
    {source middle target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        fourth)
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp first tail)
        (TraceCorQHom.add
          (TraceCorQHom.comp second tail)
          (TraceCorQHom.add
            (TraceCorQHom.comp third tail)
            (TraceCorQHom.comp fourth tail))) :=
  TraceCorQHom.add_add_add_comp
    first
    second
    third
    fourth
    tail

/-- Public wrapper: compose a right-associated four-summand source sum on the right. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_add_add_comp_right
    {source middle target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth)))
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp first tail)
        (TraceCorQHom.add
          (TraceCorQHom.comp second tail)
          (TraceCorQHom.add
            (TraceCorQHom.comp third tail)
            (TraceCorQHom.comp fourth tail))) :=
  TraceCorQHom.add_add_add_comp_right
    first
    second
    third
    fourth
    tail

/-- Public wrapper: compose on a left-associated three-summand target sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_add_add
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (first second third : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third) =
      TraceCorQHom.add
        (TraceCorQHom.comp head first)
        (TraceCorQHom.add
          (TraceCorQHom.comp head second)
          (TraceCorQHom.comp head third)) :=
  TraceCorQHom.comp_add_add
    head
    first
    second
    third

/-- Public wrapper: compose on a right-associated three-summand target sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_add_add_right
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (first second third : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second third)) =
      TraceCorQHom.add
        (TraceCorQHom.comp head first)
        (TraceCorQHom.add
          (TraceCorQHom.comp head second)
          (TraceCorQHom.comp head third)) :=
  TraceCorQHom.comp_add_add_right
    head
    first
    second
    third

/-- Public wrapper: compose on a left-associated four-summand target sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_add_add_add
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.add
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        fourth) =
      TraceCorQHom.add
        (TraceCorQHom.comp head first)
        (TraceCorQHom.add
          (TraceCorQHom.comp head second)
          (TraceCorQHom.add
            (TraceCorQHom.comp head third)
            (TraceCorQHom.comp head fourth))) :=
  TraceCorQHom.comp_add_add_add
    head
    first
    second
    third
    fourth

/-- Public wrapper: compose on a right-associated four-summand target sum. -/
theorem AnalyticMotivesRoot.traceCorQHom_comp_add_add_add_right
    {source middle target : TraceCorQObject}
    (head : TraceCorQHom source middle)
    (first second third fourth : TraceCorQHom middle target) :
    TraceCorQHom.comp
      head
      (TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth))) =
      TraceCorQHom.add
        (TraceCorQHom.comp head first)
        (TraceCorQHom.add
          (TraceCorQHom.comp head second)
          (TraceCorQHom.add
            (TraceCorQHom.comp head third)
            (TraceCorQHom.comp head fourth))) :=
  TraceCorQHom.comp_add_add_add_right
    head
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary
