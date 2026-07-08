import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Distribution.Owner

/-!
# Public sign distribution normal forms for typed trace homs

This file exposes negation distribution through three- and four-summand typed
trace-correspondence hom sums.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root distributes negation over left-associated three-summand sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_add_three_left
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
  TraceCorQHom.neg_add_three_left
    first
    second
    third

/-- The top root distributes negation over right-associated three-summand sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_add_three_right
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
  TraceCorQHom.neg_add_three_right
    first
    second
    third

/-- The top root distributes negation over left-associated four-summand sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_add_four_left
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
  TraceCorQHom.neg_add_four_left
    first
    second
    third
    fourth

/-- The top root distributes negation over right-associated four-summand sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_neg_add_four_right
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
  TraceCorQHom.neg_add_four_right
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary
