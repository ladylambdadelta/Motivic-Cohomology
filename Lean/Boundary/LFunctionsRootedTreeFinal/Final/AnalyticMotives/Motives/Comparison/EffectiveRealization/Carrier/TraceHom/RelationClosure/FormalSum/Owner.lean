import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.QuotientCandidate.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Owner

/-!
# Formal-sum relation-closure carriers for analytic effective realization

This file exposes the finite relation-closure constructors that normalize raw
formal sums: same-formal-sum transport, permutation, adjacent cancellation,
and adjacent same-generator coefficient combination.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Same-formal-sum relation-closure derivation at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureSameFormalSum
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (formalSum_eq : left.formalSum = right.formalSum) :
    TraceCorQRelationClosure ledger left right :=
  TraceCorQRelationClosure.sameFormalSumDerivation
    ledger
    left
    right
    formalSum_eq

/-- Permuted-formal-sum relation-closure derivation at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosurePermFormalSum
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    TraceCorQRelationClosure ledger left right :=
  TraceCorQRelationClosure.permFormalSumDerivation
    ledger
    left
    right
    formalSum_perm

/-- Adjacent opposite coefficient cancellation at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureCancelAdjacentOpposite
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQRelationClosure
      ledger
      (TraceCorQQuotientInput.ofFormalSumLedger
        (leftContext ++
          (coefficient, generator) ::
            (-coefficient, generator) ::
              suffix)
        ledger)
      (TraceCorQQuotientInput.ofFormalSumLedger
        (leftContext ++ suffix)
        ledger) :=
  TraceCorQRelationClosure.cancelAdjacentOppositeDerivation
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- Adjacent same-generator coefficient combination at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureCombineAdjacentSame
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQRelationClosure
      ledger
      (TraceCorQQuotientInput.ofFormalSumLedger
        (leftContext ++
          (leftCoefficient, generator) ::
            (rightCoefficient, generator) ::
              suffix)
        ledger)
      (TraceCorQQuotientInput.ofFormalSumLedger
        (leftContext ++
          (leftCoefficient + rightCoefficient, generator) ::
            suffix)
        ledger) :=
  TraceCorQRelationClosure.combineAdjacentSameDerivation
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- Same-formal-sum boundary derivation is the existing same-formal-sum constructor. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureSameFormalSum_eq
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (formalSum_eq : left.formalSum = right.formalSum) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureSameFormalSum
      ledger
      left
      right
      formalSum_eq =
      TraceCorQRelationClosure.sameFormalSum
        ledger
        left
        right
        formalSum_eq :=
  rfl

/-- Permuted-formal-sum boundary derivation is the existing permutation constructor. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosurePermFormalSum_eq
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosurePermFormalSum
      ledger
      left
      right
      formalSum_perm =
      TraceCorQRelationClosure.permFormalSum
        ledger
        left
        right
        formalSum_perm :=
  rfl

/-- Adjacent opposite cancellation boundary derivation is the existing constructor. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureCancelAdjacentOpposite_eq
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureCancelAdjacentOpposite
      ledger
      leftContext
      suffix
      coefficient
      generator =
      TraceCorQRelationClosure.cancelAdjacentOpposite
        ledger
        leftContext
        suffix
        coefficient
        generator :=
  rfl

/-- Adjacent same-generator combination boundary derivation is the existing constructor. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureCombineAdjacentSame_eq
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureCombineAdjacentSame
      ledger
      leftContext
      suffix
      leftCoefficient
      rightCoefficient
      generator =
      TraceCorQRelationClosure.combineAdjacentSame
        ledger
        leftContext
        suffix
        leftCoefficient
        rightCoefficient
        generator :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
