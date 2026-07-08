import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Core.Owner

/-!
# Ledger projections for quotient relation witnesses

This file owns ledger projection facts for concrete quotient relation witness
constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The ledger projection of a built relation witness is the supplied ledger. -/
theorem TraceCorQRelationWitness.ofLedgerDerivation_ledger
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).ledger =
      ledger :=
  rfl

/-- Reflexive relation witnesses use the empty ledger. -/
theorem TraceCorQRelationWitness.refl_ledger
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).ledger =
      TraceCorQRelationLedger.empty :=
  rfl

/-- Symmetry preserves the witness ledger. -/
theorem TraceCorQRelationWitness.symm_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).ledger =
      witness.ledger :=
  rfl

/-- Transitivity appends witness ledgers. -/
theorem TraceCorQRelationWitness.trans_ledger
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).ledger =
      TraceCorQRelationLedger.append first.ledger second.ledger :=
  rfl

/-- Additive compatibility appends witness ledgers. -/
theorem TraceCorQRelationWitness.addCongr_ledger
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).ledger =
      TraceCorQRelationLedger.append
        leftWitness.ledger
        rightWitness.ledger :=
  rfl

/-- Scalar compatibility preserves witness ledgers. -/
theorem TraceCorQRelationWitness.smulCongr_ledger
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).ledger =
      witness.ledger :=
  rfl

/-- Composition compatibility appends witness ledgers. -/
theorem TraceCorQRelationWitness.compCongr_ledger
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).ledger =
      TraceCorQRelationLedger.append
        leftWitness.ledger
        rightWitness.ledger :=
  rfl

/-- Same-formal-sum witnesses carry the supplied ledger. -/
theorem TraceCorQRelationWitness.sameFormalSum_ledger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).ledger =
      ledger :=
  rfl

/-- Permuted-formal-sum witnesses carry the supplied ledger. -/
theorem TraceCorQRelationWitness.permFormalSum_ledger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).ledger =
      ledger :=
  rfl

/-- Adjacent opposite coefficient cancellation witnesses carry the supplied ledger. -/
theorem TraceCorQRelationWitness.cancelAdjacentOpposite_ledger
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
  rfl

/-- Adjacent same-generator coefficient-combination witnesses carry the supplied ledger. -/
theorem TraceCorQRelationWitness.combineAdjacentSame_ledger
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
  rfl

/-- Endpoint transport preserves the witness ledger. -/
theorem TraceCorQRelationWitness.transportEndpoints_ledger
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
  rfl
end AnalyticMotives
end LFunctions
end Boundary
