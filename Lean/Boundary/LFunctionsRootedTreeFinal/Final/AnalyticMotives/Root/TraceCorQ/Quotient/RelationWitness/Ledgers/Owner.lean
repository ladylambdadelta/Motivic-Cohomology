import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Ledgers.Owner

/-!
# Top-root relation-witness ledger projections

This file exposes ledger projections for concrete relation-witness
constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes ledgers of built relation witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_ofLedgerDerivation_ledger
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).ledger =
      ledger :=
  TraceCorQ.relationWitness_ofLedgerDerivation_ledger
    ledger
    derivation

/-- The top root exposes ledgers of reflexive witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_refl_ledger
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).ledger =
      TraceCorQRelationLedger.empty :=
  TraceCorQ.relationWitness_refl_ledger
    candidate

/-- The top root exposes ledgers of symmetric witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_symm_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).ledger =
      witness.ledger :=
  TraceCorQ.relationWitness_symm_ledger
    witness

/-- The top root exposes ledgers of transitive witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_trans_ledger
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).ledger =
      TraceCorQRelationLedger.append first.ledger second.ledger :=
  TraceCorQ.relationWitness_trans_ledger
    first
    second

/-- The top root exposes ledgers of additive-compatible witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_addCongr_ledger
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).ledger =
      TraceCorQRelationLedger.append
        leftWitness.ledger
        rightWitness.ledger :=
  TraceCorQ.relationWitness_addCongr_ledger
    leftWitness
    rightWitness

/-- The top root exposes ledgers of scalar-compatible witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_smulCongr_ledger
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).ledger =
      witness.ledger :=
  TraceCorQ.relationWitness_smulCongr_ledger
    coefficient
    witness

/-- The top root exposes ledgers of composition-compatible witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_compCongr_ledger
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).ledger =
      TraceCorQRelationLedger.append
        leftWitness.ledger
        rightWitness.ledger :=
  TraceCorQ.relationWitness_compCongr_ledger
    leftWitness
    rightWitness

/-- The top root exposes ledgers of same-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_sameFormalSum_ledger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).ledger =
      ledger :=
  TraceCorQ.relationWitness_sameFormalSum_ledger
    ledger
    formalSum_eq

/-- The top root exposes ledgers of permuted-formal-sum witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_permFormalSum_ledger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).ledger =
      ledger :=
  TraceCorQ.relationWitness_permFormalSum_ledger
    ledger
    formalSum_perm

/-- The top root exposes ledgers of adjacent opposite-coefficient cancellation witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_cancelAdjacentOpposite_ledger
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.cancelAdjacentOpposite
      ledger
      leftContext
      suffix
      coefficient
      generator).ledger =
      ledger :=
  TraceCorQ.relationWitness_cancelAdjacentOpposite_ledger
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The top root exposes ledgers of adjacent same-generator combination witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_combineAdjacentSame_ledger
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.combineAdjacentSame
      ledger
      leftContext
      suffix
      leftCoefficient
      rightCoefficient
      generator).ledger =
      ledger :=
  TraceCorQ.relationWitness_combineAdjacentSame_ledger
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The top root exposes ledgers of endpoint-transported witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_transportEndpoints_ledger
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    (TraceCorQRelationWitness.transportEndpoints
      left_eq
      right_eq
      witness).ledger =
      witness.ledger :=
  TraceCorQ.relationWitness_transportEndpoints_ledger
    left_eq
    right_eq
    witness

end AnalyticMotives
end LFunctions
end Boundary
