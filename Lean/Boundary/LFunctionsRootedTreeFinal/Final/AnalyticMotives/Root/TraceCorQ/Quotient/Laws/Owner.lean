import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Laws.Owner

/-!
# Top-root quotient trace-correspondence laws

This file exposes concrete quotient laws through the top-level
`AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes same-formal-sum quotient soundness. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_sound_sameFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (same : left.formalSum = right.formalSum) :
    TraceCorQQuotient.ofCandidate left =
      TraceCorQQuotient.ofCandidate right :=
  TraceCorQ.quotient_sound_sameFormalSum
    ledger
    same

/-- The top root exposes quotient zero as the empty candidate class. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_zero_eq_ofCandidate_empty :
    TraceCorQQuotient.zero =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  TraceCorQ.quotient_zero_eq_ofCandidate_empty

/-- The top root exposes the left zero law for quotient addition. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_zero_add
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      TraceCorQQuotient.zero
      candidateClass =
      candidateClass :=
  TraceCorQ.quotient_zero_add
    candidateClass

/-- The top root exposes the right zero law for quotient addition. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_add_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      candidateClass
      TraceCorQQuotient.zero =
      candidateClass :=
  TraceCorQ.quotient_add_zero
    candidateClass

/-- The top root exposes scalar multiplication on quotient representatives. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_smul_ofCandidate
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.smul
        coefficient
        (TraceCorQQuotient.ofCandidate candidate) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.smul coefficient candidate) :=
  TraceCorQ.quotient_smul_ofCandidate
    coefficient
    candidate

/-- The top root exposes scalar multiplication of quotient zero. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_smul_zero
    (coefficient : Rat) :
    TraceCorQQuotient.smul
      coefficient
      TraceCorQQuotient.zero =
      TraceCorQQuotient.zero :=
  TraceCorQ.quotient_smul_zero
    coefficient

/-- The top root exposes the quotient scalar identity law. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_one_smul
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul 1 candidateClass =
      candidateClass :=
  TraceCorQ.quotient_one_smul
    candidateClass

/-- The top root exposes quotient scalar associativity. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      leftCoefficient
      (TraceCorQQuotient.smul rightCoefficient candidateClass) =
      TraceCorQQuotient.smul
        (leftCoefficient * rightCoefficient)
        candidateClass :=
  TraceCorQ.quotient_smul_smul
    leftCoefficient
    rightCoefficient
    candidateClass

/-- The top root exposes quotient composition on representatives. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_comp_ofCandidate
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.comp
        (TraceCorQQuotient.ofCandidate left)
        (TraceCorQQuotient.ofCandidate right) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.comp left right) :=
  TraceCorQ.quotient_comp_ofCandidate
    left
    right

/-- The top root exposes standard zero notation for quotient classes. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_inst_zero_eq :
    (0 : TraceCorQQuotient) =
      TraceCorQQuotient.zero :=
  TraceCorQ.quotient_inst_zero_eq

/-- The top root exposes standard addition notation for quotient classes. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_inst_add_eq
    (left right : TraceCorQQuotient) :
    left + right =
      TraceCorQQuotient.add left right :=
  TraceCorQ.quotient_inst_add_eq
    left
    right

/-- The top root exposes standard scalar notation for quotient classes. -/
theorem AnalyticMotivesRoot.traceCorQQuotient_inst_smul_eq
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    coefficient • candidateClass =
      TraceCorQQuotient.smul coefficient candidateClass :=
  TraceCorQ.quotient_inst_smul_eq
    coefficient
    candidateClass

end AnalyticMotives
end LFunctions
end Boundary
