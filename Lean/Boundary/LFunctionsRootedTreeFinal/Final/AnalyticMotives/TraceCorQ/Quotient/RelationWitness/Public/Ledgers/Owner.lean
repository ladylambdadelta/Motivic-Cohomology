import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Ledgers.Owner

/-!
# Public relation-witness ledger projections

This file exposes ledger projection facts for concrete relation witnesses under
the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes ledgers of built relation witnesses. -/
theorem TraceCorQ.relationWitness_ofLedgerDerivation_ledger
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation ledger derivation).ledger =
      ledger :=
  TraceCorQRelationWitness.ofLedgerDerivation_ledger
    ledger
    derivation

/-- The trace-correspondence root exposes ledgers of reflexive witnesses. -/
theorem TraceCorQ.relationWitness_refl_ledger
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).ledger =
      TraceCorQRelationLedger.empty :=
  TraceCorQRelationWitness.refl_ledger
    candidate

/-- The trace-correspondence root exposes ledgers of symmetric witnesses. -/
theorem TraceCorQ.relationWitness_symm_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).ledger =
      witness.ledger :=
  TraceCorQRelationWitness.symm_ledger
    witness

/-- The trace-correspondence root exposes ledgers of transitive witnesses. -/
theorem TraceCorQ.relationWitness_trans_ledger
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).ledger =
      TraceCorQRelationLedger.append first.ledger second.ledger :=
  TraceCorQRelationWitness.trans_ledger
    first
    second

/-- The trace-correspondence root exposes ledgers of additive-compatible witnesses. -/
theorem TraceCorQ.relationWitness_addCongr_ledger
    {leftOne leftTwo rightOne rightTwo : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftOne leftTwo)
    (rightWitness : TraceCorQRelationWitness rightOne rightTwo) :
    (TraceCorQRelationWitness.addCongr leftWitness rightWitness).ledger =
      TraceCorQRelationLedger.append
        leftWitness.ledger
        rightWitness.ledger :=
  TraceCorQRelationWitness.addCongr_ledger
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes ledgers of scalar-compatible witnesses. -/
theorem TraceCorQ.relationWitness_smulCongr_ledger
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr coefficient witness).ledger =
      witness.ledger :=
  TraceCorQRelationWitness.smulCongr_ledger
    coefficient
    witness

/-- The trace-correspondence root exposes ledgers of composition-compatible witnesses. -/
theorem TraceCorQ.relationWitness_compCongr_ledger
    {leftOne leftTwo rightOne rightTwo : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftOne leftTwo)
    (rightWitness : TraceCorQRelationWitness rightOne rightTwo) :
    (TraceCorQRelationWitness.compCongr leftWitness rightWitness).ledger =
      TraceCorQRelationLedger.append
        leftWitness.ledger
        rightWitness.ledger :=
  TraceCorQRelationWitness.compCongr_ledger
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes ledgers of same-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_sameFormalSum_ledger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum ledger formalSum_eq).ledger =
      ledger :=
  TraceCorQRelationWitness.sameFormalSum_ledger
    ledger
    formalSum_eq

/-- The trace-correspondence root exposes ledgers of permuted-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_permFormalSum_ledger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum ledger formalSum_perm).ledger =
      ledger :=
  TraceCorQRelationWitness.permFormalSum_ledger
    ledger
    formalSum_perm

/-- The trace-correspondence root exposes ledgers of adjacent opposite-coefficient cancellation witnesses. -/
theorem TraceCorQ.relationWitness_cancelAdjacentOpposite_ledger
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
  TraceCorQRelationWitness.cancelAdjacentOpposite_ledger
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The trace-correspondence root exposes ledgers of adjacent same-generator combination witnesses. -/
theorem TraceCorQ.relationWitness_combineAdjacentSame_ledger
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
  TraceCorQRelationWitness.combineAdjacentSame_ledger
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The trace-correspondence root exposes ledgers of endpoint-transported witnesses. -/
theorem TraceCorQ.relationWitness_transportEndpoints_ledger
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
  TraceCorQRelationWitness.transportEndpoints_ledger
    left_eq
    right_eq
    witness

end AnalyticMotives
end LFunctions
end Boundary
