import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Core.Owner

/-!
# Public relation-witness core

This file exposes concrete finite relation witnesses under the `TraceCorQ`
aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes relation-witness ledgers. -/
def TraceCorQ.relationWitness_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationLedger :=
  TraceCorQRelationWitness.ledger
    witness

/-- The trace-correspondence root exposes relation-witness derivations. -/
def TraceCorQ.relationWitness_derivation
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationClosure witness.ledger left right :=
  TraceCorQRelationWitness.derivation
    witness

/-- The trace-correspondence root exposes relation witnesses built from ledgers and derivations. -/
def TraceCorQ.relationWitness_ofLedgerDerivation
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationWitness left right :=
  TraceCorQRelationWitness.ofLedgerDerivation
    ledger
    derivation

/-- The trace-correspondence root exposes reflexive relation witnesses. -/
def TraceCorQ.relationWitness_refl
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationWitness candidate candidate :=
  TraceCorQRelationWitness.refl
    candidate

/-- The trace-correspondence root exposes symmetric relation witnesses. -/
def TraceCorQ.relationWitness_symm
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationWitness right left :=
  TraceCorQRelationWitness.symm
    witness

/-- The trace-correspondence root exposes transitive relation witnesses. -/
def TraceCorQ.relationWitness_trans
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    TraceCorQRelationWitness left right :=
  TraceCorQRelationWitness.trans
    first
    second

/-- The trace-correspondence root exposes additive compatibility for relation witnesses. -/
def TraceCorQ.relationWitness_addCongr
    {leftOne leftTwo rightOne rightTwo : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftOne leftTwo)
    (rightWitness : TraceCorQRelationWitness rightOne rightTwo) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.add leftOne rightOne)
      (TraceCorQQuotientCandidate.add leftTwo rightTwo) :=
  TraceCorQRelationWitness.addCongr
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes scalar compatibility for relation witnesses. -/
def TraceCorQ.relationWitness_smulCongr
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.smul coefficient left)
      (TraceCorQQuotientCandidate.smul coefficient right) :=
  TraceCorQRelationWitness.smulCongr
    coefficient
    witness

/-- The trace-correspondence root exposes composition compatibility for relation witnesses. -/
def TraceCorQ.relationWitness_compCongr
    {leftOne leftTwo rightOne rightTwo : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness leftOne leftTwo)
    (rightWitness : TraceCorQRelationWitness rightOne rightTwo) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.comp leftOne rightOne)
      (TraceCorQQuotientCandidate.comp leftTwo rightTwo) :=
  TraceCorQRelationWitness.compCongr
    leftWitness
    rightWitness

/-- The trace-correspondence root exposes same-formal-sum witnesses. -/
def TraceCorQ.relationWitness_sameFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    TraceCorQRelationWitness left right :=
  TraceCorQRelationWitness.sameFormalSum
    ledger
    formalSum_eq

/-- The trace-correspondence root exposes permuted-formal-sum witnesses. -/
def TraceCorQ.relationWitness_permFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    TraceCorQRelationWitness left right :=
  TraceCorQRelationWitness.permFormalSum
    ledger
    formalSum_perm

/-- The trace-correspondence root exposes adjacent opposite-coefficient cancellation witnesses. -/
def TraceCorQ.relationWitness_cancelAdjacentOpposite
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQRelationWitness
      (TraceCorQQuotientInput.ofFormalSumLedger
        (leftContext ++
          (coefficient, generator) ::
            (-coefficient, generator) ::
              suffix)
        ledger)
      (TraceCorQQuotientInput.ofFormalSumLedger
        (leftContext ++ suffix)
        ledger) :=
  TraceCorQRelationWitness.cancelAdjacentOpposite
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The trace-correspondence root exposes adjacent same-generator coefficient-combination witnesses. -/
def TraceCorQ.relationWitness_combineAdjacentSame
    (ledger : TraceCorQRelationLedger)
    (leftContext suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQRelationWitness
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
  TraceCorQRelationWitness.combineAdjacentSame
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The trace-correspondence root exposes endpoint transport for relation witnesses. -/
def TraceCorQ.relationWitness_transportEndpoints
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    TraceCorQRelationWitness targetLeft targetRight :=
  TraceCorQRelationWitness.transportEndpoints
    left_eq
    right_eq
    witness

end AnalyticMotives
end LFunctions
end Boundary
