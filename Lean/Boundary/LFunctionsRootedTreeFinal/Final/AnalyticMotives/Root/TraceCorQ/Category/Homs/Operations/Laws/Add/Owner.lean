import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Full.Owner

/-!
# Public higher additive normal forms for typed trace homs

This file exposes four-summand additive reassociation normal forms for typed
trace-correspondence hom classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root normalizes fully left-associated four-summand typed hom sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_assoc_four_left
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
  TraceCorQHom.add_assoc_four_left
    first
    second
    third
    fourth

/-- The top root normalizes middle-left four-summand typed hom sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_assoc_four_middle_left
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
  TraceCorQHom.add_assoc_four_middle_left
    first
    second
    third
    fourth

/-- The top root normalizes binary-split four-summand typed hom sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_assoc_four_binary
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
  TraceCorQHom.add_assoc_four_binary
    first
    second
    third
    fourth

/-- The top root normalizes middle-right four-summand typed hom sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_assoc_four_middle_right
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
  TraceCorQHom.add_assoc_four_middle_right
    first
    second
    third
    fourth

/-- The top root exposes that right-associated four-summand typed hom sums are normal. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_assoc_four_right
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
  TraceCorQHom.add_assoc_four_right
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary
