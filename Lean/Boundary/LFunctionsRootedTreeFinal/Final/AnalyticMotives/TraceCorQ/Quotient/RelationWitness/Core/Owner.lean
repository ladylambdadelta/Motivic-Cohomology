import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Additivity.Owner

/-!
# Relation witnesses for quotient candidates

This file owns concrete witnesses that two quotient candidates are related by
finite relation-closure derivations.

Each witness stores the ledger and the derivation.  It is setoid-ready data,
but it is not itself a quotient relation and does not introduce quotient
classes.  Ledger projection facts live in the `Ledgers` child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A concrete finite relation witness between two quotient candidates. -/
abbrev TraceCorQRelationWitness
    (left right : TraceCorQQuotientCandidate) :=
  Sigma (fun ledger =>
    TraceCorQRelationClosure ledger left right)

/-- The ledger carried by a relation witness. -/
def TraceCorQRelationWitness.ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationLedger :=
  witness.1

/-- The derivation carried by a relation witness. -/
def TraceCorQRelationWitness.derivation
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationClosure witness.ledger left right :=
  witness.2

/-- Build a relation witness from a ledger and derivation. -/
def TraceCorQRelationWitness.ofLedgerDerivation
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationWitness left right :=
  Sigma.mk ledger derivation

/-- Reflexive relation witness for a quotient candidate. -/
def TraceCorQRelationWitness.refl
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationWitness candidate candidate :=
  TraceCorQRelationWitness.ofLedgerDerivation
    TraceCorQRelationLedger.empty
    (TraceCorQRelationClosure.emptyRefl candidate)

/-- Symmetry for concrete relation witnesses. -/
def TraceCorQRelationWitness.symm
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationWitness right left :=
  TraceCorQRelationWitness.ofLedgerDerivation
    witness.ledger
    (TraceCorQRelationClosure.symmDerivation
      witness.ledger
      left
      right
      witness.derivation)

/-- Transitivity for concrete relation witnesses. -/
def TraceCorQRelationWitness.trans
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    TraceCorQRelationWitness left right :=
  TraceCorQRelationWitness.ofLedgerDerivation
    (TraceCorQRelationLedger.append first.ledger second.ledger)
    (TraceCorQRelationClosure.transDerivation
      first.ledger
      second.ledger
      left
      middle
      right
      first.derivation
      second.derivation)

/-- Additive compatibility for concrete relation witnesses. -/
def TraceCorQRelationWitness.addCongr
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.add left₁ right₁)
      (TraceCorQQuotientCandidate.add left₂ right₂) :=
  TraceCorQRelationWitness.ofLedgerDerivation
    (TraceCorQRelationLedger.append
      leftWitness.ledger
      rightWitness.ledger)
    (TraceCorQRelationClosure.addCongrDerivation
      leftWitness.ledger
      rightWitness.ledger
      left₁
      left₂
      right₁
      right₂
      leftWitness.derivation
      rightWitness.derivation)

/-- Scalar compatibility for concrete relation witnesses. -/
def TraceCorQRelationWitness.smulCongr
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.smul coefficient left)
      (TraceCorQQuotientCandidate.smul coefficient right) :=
  TraceCorQRelationWitness.ofLedgerDerivation
    witness.ledger
    (TraceCorQRelationClosure.smulCongrDerivation
      witness.ledger
      coefficient
      left
      right
      witness.derivation)

/-- Composition compatibility for concrete relation witnesses. -/
def TraceCorQRelationWitness.compCongr
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.comp left₁ right₁)
      (TraceCorQQuotientCandidate.comp left₂ right₂) :=
  TraceCorQRelationWitness.ofLedgerDerivation
    (TraceCorQRelationLedger.append
      leftWitness.ledger
      rightWitness.ledger)
    (TraceCorQRelationClosure.compCongrDerivation
      leftWitness.ledger
      rightWitness.ledger
      left₁
      left₂
      right₁
      right₂
      leftWitness.derivation
      rightWitness.derivation)

/-- A concrete witness that same-formal-sum candidates are related. -/
def TraceCorQRelationWitness.sameFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    TraceCorQRelationWitness left right :=
  TraceCorQRelationWitness.ofLedgerDerivation
    ledger
    (TraceCorQRelationClosure.sameFormalSumDerivation
      ledger
      left
      right
      formalSum_eq)

/-- A concrete witness that permuted-formal-sum candidates are related. -/
def TraceCorQRelationWitness.permFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    TraceCorQRelationWitness left right :=
  TraceCorQRelationWitness.ofLedgerDerivation
    ledger
    (TraceCorQRelationClosure.permFormalSumDerivation
      ledger
      left
      right
      formalSum_perm)

/-- A concrete witness for adjacent opposite coefficient cancellation. -/
def TraceCorQRelationWitness.cancelAdjacentOpposite
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
  TraceCorQRelationWitness.ofLedgerDerivation
    ledger
    (TraceCorQRelationClosure.cancelAdjacentOppositeDerivation
      ledger
      leftContext
      suffix
      coefficient
      generator)

/-- A concrete witness for adjacent same-generator coefficient combination. -/
def TraceCorQRelationWitness.combineAdjacentSame
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
  TraceCorQRelationWitness.ofLedgerDerivation
    ledger
    (TraceCorQRelationClosure.combineAdjacentSameDerivation
      ledger
      leftContext
      suffix
      leftCoefficient
      rightCoefficient
      generator)

/-- Transport a concrete relation witness along endpoint equalities. -/
def TraceCorQRelationWitness.transportEndpoints
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    TraceCorQRelationWitness targetLeft targetRight :=
  TraceCorQRelationWitness.ofLedgerDerivation
    witness.ledger
    (TraceCorQRelationClosure.transportEndpoints
      left_eq
      right_eq
      witness.derivation)

end AnalyticMotives
end LFunctions
end Boundary

