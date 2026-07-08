import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Facade.Structures.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Laws.Owner

/-!
# Trace-correspondence quotient facade

This file exposes the public root quotient soundness and algebra laws for
`TraceCorQ`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes quotient soundness. -/
theorem TraceCorQ.quotient_sound
    {left right : TraceCorQQuotientCandidate}
    (relation : TraceCorQQuotientRelation left right) :
    TraceCorQQuotient.ofCandidate left =
      TraceCorQQuotient.ofCandidate right :=
  TraceCorQQuotientRoot.sound
    relation

/-- The trace-correspondence root exposes quotient additive commutativity. -/
theorem TraceCorQ.quotient_add_comm
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.add left right =
      TraceCorQQuotient.add right left :=
  TraceCorQQuotientRoot.add_comm
    left
    right

/-- The trace-correspondence root exposes quotient additive associativity. -/
theorem TraceCorQ.quotient_add_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.add
        (TraceCorQQuotient.add left middle)
        right =
      TraceCorQQuotient.add
        left
        (TraceCorQQuotient.add middle right) :=
  TraceCorQQuotientRoot.add_assoc
    left
    middle
    right

/-- The trace-correspondence root exposes quotient scalar distributivity over addition. -/
theorem TraceCorQ.quotient_smul_add
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add left right) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient left)
        (TraceCorQQuotient.smul coefficient right) :=
  TraceCorQQuotientRoot.smul_add
    coefficient
    left
    right

/-- The trace-correspondence root exposes quotient composition associativity. -/
theorem TraceCorQ.quotient_comp_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
        (TraceCorQQuotient.comp left middle)
        right =
      TraceCorQQuotient.comp
        left
        (TraceCorQQuotient.comp middle right) :=
  TraceCorQQuotientRoot.comp_assoc
    left
    middle
    right

end AnalyticMotives
end LFunctions
end Boundary
