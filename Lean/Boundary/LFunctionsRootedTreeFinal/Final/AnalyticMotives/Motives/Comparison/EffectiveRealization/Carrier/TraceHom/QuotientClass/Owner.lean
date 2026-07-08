import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RawQuotientRelation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Setoid.Owner

/-!
# Quotient-class carriers for analytic effective realization

This file exposes the raw ambient quotient class of trace correspondences:
quotient candidates modulo the finite-witness relation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual trace-correspondence quotient class. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientClassCarrier
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient :=
  candidateClass

/-- The quotient class represented by a raw quotient candidate. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient :=
  TraceCorQQuotient.ofCandidate candidate

/-- The quotient-class carrier is definitionally the supplied class. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientClassCarrier_eq
    (candidateClass : TraceCorQQuotient) :
    TraceAnalyticEffectiveRealization.traceHomQuotientClassCarrier candidateClass =
      candidateClass :=
  rfl

/-- A raw quotient relation gives equality of quotient classes. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientClassSound
    {left right : TraceCorQQuotientCandidate}
    (relation : TraceCorQQuotientRelation left right) :
    TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate left =
      TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate right :=
  TraceCorQQuotient.sound
    relation

/-- Same-formal-sum candidates define the same quotient class. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientClassSound_sameFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate left =
      TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate right :=
  TraceCorQQuotient.sound_sameFormalSum
    ledger
    formalSum_eq

/-- Permuted-formal-sum candidates define the same quotient class. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientClassSound_permFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate left =
      TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate right :=
  TraceCorQQuotient.sound_permFormalSum
    ledger
    formalSum_perm

/-- Adjacent opposite rational multiples cancel in the quotient class. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientClassSound_cancelAdjacentOpposite
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate
      (TraceCorQQuotientInput.ofFormalSumLedger
        (leftContext ++
          (coefficient, generator) ::
            (-coefficient, generator) ::
              suffix)
        ledger) =
      TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate
        (TraceCorQQuotientInput.ofFormalSumLedger
          (leftContext ++ suffix)
          ledger) :=
  TraceCorQQuotient.sound_cancelAdjacentOpposite
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- Adjacent rational multiples of the same generator combine in the quotient class. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientClassSound_combineAdjacentSame
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate
      (TraceCorQQuotientInput.ofFormalSumLedger
        (leftContext ++
          (leftCoefficient, generator) ::
            (rightCoefficient, generator) ::
              suffix)
        ledger) =
      TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate
        (TraceCorQQuotientInput.ofFormalSumLedger
          (leftContext ++
            (leftCoefficient + rightCoefficient, generator) ::
              suffix)
          ledger) :=
  TraceCorQQuotient.sound_combineAdjacentSame
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

end AnalyticMotives
end LFunctions
end Boundary
