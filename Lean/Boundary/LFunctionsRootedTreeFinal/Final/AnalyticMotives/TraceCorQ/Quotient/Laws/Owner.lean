import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Owner

/-!
# Public quotient trace-correspondence laws

This file exposes concrete quotient laws under the `TraceCorQ` aggregate
namespace without growing the main trace-correspondence owner.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes same-formal-sum quotient soundness. -/
theorem TraceCorQ.quotient_sound_sameFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (same : left.formalSum = right.formalSum) :
    TraceCorQQuotient.ofCandidate left =
      TraceCorQQuotient.ofCandidate right :=
  TraceCorQQuotientRoot.sound_sameFormalSum
    ledger
    same

/-- The trace-correspondence root exposes quotient zero as the empty candidate class. -/
theorem TraceCorQ.quotient_zero_eq_ofCandidate_empty :
    TraceCorQQuotient.zero =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  TraceCorQQuotientRoot.zero_eq_ofCandidate_empty

/-- The trace-correspondence root exposes the left zero law for quotient addition. -/
theorem TraceCorQ.quotient_zero_add
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      TraceCorQQuotient.zero
      candidateClass =
      candidateClass :=
  TraceCorQQuotientRoot.zero_add
    candidateClass

/-- The trace-correspondence root exposes the right zero law for quotient addition. -/
theorem TraceCorQ.quotient_add_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      candidateClass
      TraceCorQQuotient.zero =
      candidateClass :=
  TraceCorQQuotientRoot.add_zero
    candidateClass

/-- The trace-correspondence root exposes scalar multiplication on quotient representatives. -/
theorem TraceCorQ.quotient_smul_ofCandidate
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.smul
        coefficient
        (TraceCorQQuotient.ofCandidate candidate) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.smul coefficient candidate) :=
  TraceCorQQuotientRoot.smul_ofCandidate
    coefficient
    candidate

/-- The trace-correspondence root exposes scalar multiplication of quotient zero. -/
theorem TraceCorQ.quotient_smul_zero
    (coefficient : Rat) :
    TraceCorQQuotient.smul
      coefficient
      TraceCorQQuotient.zero =
      TraceCorQQuotient.zero :=
  TraceCorQQuotientRoot.smul_zero
    coefficient

/-- The trace-correspondence root exposes the quotient scalar identity law. -/
theorem TraceCorQ.quotient_one_smul
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul 1 candidateClass =
      candidateClass :=
  TraceCorQQuotientRoot.one_smul
    candidateClass

/-- The trace-correspondence root exposes quotient scalar associativity. -/
theorem TraceCorQ.quotient_smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      leftCoefficient
      (TraceCorQQuotient.smul rightCoefficient candidateClass) =
      TraceCorQQuotient.smul
        (leftCoefficient * rightCoefficient)
        candidateClass :=
  TraceCorQQuotientRoot.smul_smul
    leftCoefficient
    rightCoefficient
    candidateClass

/-- The trace-correspondence root exposes quotient composition on representatives. -/
theorem TraceCorQ.quotient_comp_ofCandidate
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.comp
        (TraceCorQQuotient.ofCandidate left)
        (TraceCorQQuotient.ofCandidate right) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.comp left right) :=
  TraceCorQQuotientRoot.comp_ofCandidate
    left
    right

/-- The trace-correspondence root exposes standard zero notation for quotient classes. -/
theorem TraceCorQ.quotient_inst_zero_eq :
    (0 : TraceCorQQuotient) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotientRoot.inst_zero_eq

/-- The trace-correspondence root exposes standard addition notation for quotient classes. -/
theorem TraceCorQ.quotient_inst_add_eq
    (left right : TraceCorQQuotient) :
    left + right =
      TraceCorQQuotient.add left right :=
  TraceCorQQuotientRoot.inst_add_eq
    left
    right

/-- The trace-correspondence root exposes standard scalar notation for quotient classes. -/
theorem TraceCorQ.quotient_inst_smul_eq
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    coefficient • candidateClass =
      TraceCorQQuotient.smul coefficient candidateClass :=
  TraceCorQQuotientRoot.inst_smul_eq
    coefficient
    candidateClass

end AnalyticMotives
end LFunctions
end Boundary
