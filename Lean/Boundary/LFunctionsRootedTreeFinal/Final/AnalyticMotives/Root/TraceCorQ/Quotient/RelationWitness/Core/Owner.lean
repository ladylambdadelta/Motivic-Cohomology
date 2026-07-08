import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Core.Owner

/-!
# Top-root relation-witness core

This file exposes the core concrete relation-witness constructors for ambient
trace-correspondence quotient candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes relation-witness ledgers. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationLedger :=
  TraceCorQ.relationWitness_ledger
    witness

/-- The top root exposes relation-witness derivations. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_derivation
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationClosure witness.ledger left right :=
  TraceCorQ.relationWitness_derivation
    witness

/-- The top root exposes relation witnesses built from ledgers and derivations. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_ofLedgerDerivation
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationWitness left right :=
  TraceCorQ.relationWitness_ofLedgerDerivation
    ledger
    derivation

/-- The top root exposes reflexive relation witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_refl
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationWitness candidate candidate :=
  TraceCorQ.relationWitness_refl
    candidate

/-- The top root exposes symmetric relation witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_symm
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationWitness right left :=
  TraceCorQ.relationWitness_symm
    witness

/-- The top root exposes transitive relation witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_trans
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    TraceCorQRelationWitness left right :=
  TraceCorQ.relationWitness_trans
    first
    second

/-- The top root exposes additive compatibility for relation witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_addCongr
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.add left₁ right₁)
      (TraceCorQQuotientCandidate.add left₂ right₂) :=
  TraceCorQ.relationWitness_addCongr
    leftWitness
    rightWitness

/-- The top root exposes scalar compatibility for relation witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_smulCongr
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.smul coefficient left)
      (TraceCorQQuotientCandidate.smul coefficient right) :=
  TraceCorQ.relationWitness_smulCongr
    coefficient
    witness

/-- The top root exposes composition compatibility for relation witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_compCongr
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.comp left₁ right₁)
      (TraceCorQQuotientCandidate.comp left₂ right₂) :=
  TraceCorQ.relationWitness_compCongr
    leftWitness
    rightWitness

/-- The top root exposes same-formal-sum witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_sameFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    TraceCorQRelationWitness left right :=
  TraceCorQ.relationWitness_sameFormalSum
    ledger
    formalSum_eq

/-- The top root exposes permuted-formal-sum witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_permFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    TraceCorQRelationWitness left right :=
  TraceCorQ.relationWitness_permFormalSum
    ledger
    formalSum_perm

/-- The top root exposes adjacent opposite-coefficient cancellation witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_cancelAdjacentOpposite
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
  TraceCorQ.relationWitness_cancelAdjacentOpposite
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The top root exposes adjacent same-generator coefficient-combination witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_combineAdjacentSame
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
  TraceCorQ.relationWitness_combineAdjacentSame
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

/-- The top root exposes endpoint transport for relation witnesses. -/
def AnalyticMotivesRoot.traceCorQRelationWitness_transportEndpoints
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    TraceCorQRelationWitness targetLeft targetRight :=
  TraceCorQ.relationWitness_transportEndpoints
    left_eq
    right_eq
    witness

end AnalyticMotives
end LFunctions
end Boundary
