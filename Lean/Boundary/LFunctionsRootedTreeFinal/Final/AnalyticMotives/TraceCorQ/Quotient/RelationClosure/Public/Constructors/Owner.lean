import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Owner

/-!
# Public relation-closure constructor derivations

This file exposes concrete finite relation-closure constructor derivations under
the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes reflexive relation-closure derivations. -/
def TraceCorQ.relationClosure_refl
    (ledger : TraceCorQRelationLedger)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure ledger candidate candidate :=
  TraceCorQRelationClosure.reflDerivation
    ledger
    candidate

/-- The trace-correspondence root exposes single-generator relation-closure steps. -/
def TraceCorQ.relationClosure_step
    (ledger : TraceCorQRelationLedger)
    (relation : TraceCorQRelationGenerator) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        (TraceCorQRelationLedger.singleton relation)
        ledger)
      (TraceCorQQuotientInput.ofFormalSumLedger
        relation.support
        (TraceCorQRelationLedger.singleton relation))
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationClosure.stepDerivation
    ledger
    relation

/-- The trace-correspondence root exposes that step derivations are primitive steps. -/
theorem TraceCorQ.relationClosure_step_eq_step
    (ledger : TraceCorQRelationLedger)
    (relation : TraceCorQRelationGenerator) :
    TraceCorQRelationClosure.stepDerivation ledger relation =
      TraceCorQRelationClosure.step ledger relation :=
  TraceCorQRelationClosure.stepDerivation_eq_step
    ledger
    relation

/-- The trace-correspondence root exposes symmetry for relation-closure derivations. -/
def TraceCorQ.relationClosure_symm
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure ledger right left :=
  TraceCorQRelationClosure.symmDerivation
    ledger
    left
    right
    derivation

/-- The trace-correspondence root exposes transitivity for relation-closure derivations. -/
def TraceCorQ.relationClosure_trans
    (firstLedger secondLedger : TraceCorQRelationLedger)
    (left middle right : TraceCorQQuotientCandidate)
    (first : TraceCorQRelationClosure firstLedger left middle)
    (second : TraceCorQRelationClosure secondLedger middle right) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append firstLedger secondLedger)
      left
      right :=
  TraceCorQRelationClosure.transDerivation
    firstLedger
    secondLedger
    left
    middle
    right
    first
    second

/-- The trace-correspondence root exposes additive compatibility for relation closures. -/
def TraceCorQ.relationClosure_addCongr
    (leftLedger rightLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate)
    (leftDerivation : TraceCorQRelationClosure leftLedger left₁ left₂)
    (rightDerivation : TraceCorQRelationClosure rightLedger right₁ right₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append leftLedger rightLedger)
      (TraceCorQQuotientCandidate.add left₁ right₁)
      (TraceCorQQuotientCandidate.add left₂ right₂) :=
  TraceCorQRelationClosure.addCongrDerivation
    leftLedger
    rightLedger
    left₁
    left₂
    right₁
    right₂
    leftDerivation
    rightDerivation

/-- The trace-correspondence root exposes scalar compatibility for relation closures. -/
def TraceCorQ.relationClosure_smulCongr
    (ledger : TraceCorQRelationLedger)
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure
      ledger
      (TraceCorQQuotientCandidate.smul coefficient left)
      (TraceCorQQuotientCandidate.smul coefficient right) :=
  TraceCorQRelationClosure.smulCongrDerivation
    ledger
    coefficient
    left
    right
    derivation

/-- The trace-correspondence root exposes composition compatibility for relation closures. -/
def TraceCorQ.relationClosure_compCongr
    (leftLedger rightLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate)
    (leftDerivation : TraceCorQRelationClosure leftLedger left₁ left₂)
    (rightDerivation : TraceCorQRelationClosure rightLedger right₁ right₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append leftLedger rightLedger)
      (TraceCorQQuotientCandidate.comp left₁ right₁)
      (TraceCorQQuotientCandidate.comp left₂ right₂) :=
  TraceCorQRelationClosure.compCongrDerivation
    leftLedger
    rightLedger
    left₁
    left₂
    right₁
    right₂
    leftDerivation
    rightDerivation

/-- The trace-correspondence root exposes same-formal-sum relation closures. -/
def TraceCorQ.relationClosure_sameFormalSum
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (formalSum_eq : left.formalSum = right.formalSum) :
    TraceCorQRelationClosure ledger left right :=
  TraceCorQRelationClosure.sameFormalSumDerivation
    ledger
    left
    right
    formalSum_eq

/-- The trace-correspondence root exposes permuted-formal-sum relation closures. -/
def TraceCorQ.relationClosure_permFormalSum
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    TraceCorQRelationClosure ledger left right :=
  TraceCorQRelationClosure.permFormalSumDerivation
    ledger
    left
    right
    formalSum_perm

/-- The trace-correspondence root exposes adjacent opposite-coefficient cancellation. -/
def TraceCorQ.relationClosure_cancelAdjacentOpposite
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

/-- The trace-correspondence root exposes adjacent same-generator coefficient combination. -/
def TraceCorQ.relationClosure_combineAdjacentSame
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

end AnalyticMotives
end LFunctions
end Boundary
