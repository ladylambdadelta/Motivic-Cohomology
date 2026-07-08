import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Distribution.Owner

/-!
# Public scalar distribution normal forms for typed trace homs

This file exposes scalar distribution through three- and four-summand typed
trace-correspondence hom sums.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root distributes scalars over left-associated three-summand sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_add_three_left
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
  TraceCorQHom.smul_add_three_left
    coefficient
    first
    second
    third

/-- The top root distributes scalars over right-associated three-summand sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_add_three_right
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
  TraceCorQHom.smul_add_three_right
    coefficient
    first
    second
    third

/-- The top root distributes scalars over left-associated four-summand sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_add_four_left
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
  TraceCorQHom.smul_add_four_left
    coefficient
    first
    second
    third
    fourth

/-- The top root distributes scalars over right-associated four-summand sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_add_four_right
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
  TraceCorQHom.smul_add_four_right
    coefficient
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary
