import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Facade.Structures.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Facade.Quotient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.Owner

/-!
# Top-root trace-correspondence quotient facade

This file exposes trace-correspondence quotient soundness and algebra laws under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes quotient soundness for trace-correspondence candidates. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_sound
    {left right : TraceCorQQuotientCandidate}
    (relation : TraceCorQQuotientRelation left right) :
    TraceCorQQuotient.ofCandidate left =
      TraceCorQQuotient.ofCandidate right :=
  TraceCorQ.quotient_sound
    relation

/-- The top root exposes quotient additive commutativity. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_add_comm
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.add left right =
      TraceCorQQuotient.add right left :=
  TraceCorQ.quotient_add_comm
    left
    right

/-- The top root exposes quotient additive associativity. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_add_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.add
        (TraceCorQQuotient.add left middle)
        right =
      TraceCorQQuotient.add
        left
        (TraceCorQQuotient.add middle right) :=
  TraceCorQ.quotient_add_assoc
    left
    middle
    right

/-- The top root exposes quotient scalar distributivity over addition. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_smul_add
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add left right) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient left)
        (TraceCorQQuotient.smul coefficient right) :=
  TraceCorQ.quotient_smul_add
    coefficient
    left
    right

/-- The top root exposes quotient composition associativity. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_comp_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
        (TraceCorQQuotient.comp left middle)
        right =
      TraceCorQQuotient.comp
        left
        (TraceCorQQuotient.comp middle right) :=
  TraceCorQ.quotient_comp_assoc
    left
    middle
    right

end AnalyticMotives
end LFunctions
end Boundary
