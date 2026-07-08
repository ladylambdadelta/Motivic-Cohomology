import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Public.Constructors.Owner

/-!
# Top-root relation-closure constructor derivations

This file exposes concrete finite relation-closure constructor derivations
through the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes reflexive relation-closure derivations. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_refl
    (ledger : TraceCorQRelationLedger)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure ledger candidate candidate :=
  TraceCorQ.relationClosure_refl
    ledger
    candidate

/-- The top root exposes single-generator relation-closure steps. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_step
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
  TraceCorQ.relationClosure_step
    ledger
    relation

/-- The top root exposes that step derivations are primitive steps. -/
theorem AnalyticMotivesRoot.traceCorQRelationClosure_step_eq_step
    (ledger : TraceCorQRelationLedger)
    (relation : TraceCorQRelationGenerator) :
    TraceCorQRelationClosure.stepDerivation ledger relation =
      TraceCorQRelationClosure.step ledger relation :=
  TraceCorQ.relationClosure_step_eq_step
    ledger
    relation

/-- The top root exposes symmetry for relation-closure derivations. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_symm
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure ledger right left :=
  TraceCorQ.relationClosure_symm
    ledger
    left
    right
    derivation

/-- The top root exposes transitivity for relation-closure derivations. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_trans
    (firstLedger secondLedger : TraceCorQRelationLedger)
    (left middle right : TraceCorQQuotientCandidate)
    (first : TraceCorQRelationClosure firstLedger left middle)
    (second : TraceCorQRelationClosure secondLedger middle right) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append firstLedger secondLedger)
      left
      right :=
  TraceCorQ.relationClosure_trans
    firstLedger
    secondLedger
    left
    middle
    right
    first
    second

/-- The top root exposes additive compatibility for relation closures. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_addCongr
    (leftLedger rightLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate)
    (leftDerivation : TraceCorQRelationClosure leftLedger left₁ left₂)
    (rightDerivation : TraceCorQRelationClosure rightLedger right₁ right₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append leftLedger rightLedger)
      (TraceCorQQuotientCandidate.add left₁ right₁)
      (TraceCorQQuotientCandidate.add left₂ right₂) :=
  TraceCorQ.relationClosure_addCongr
    leftLedger
    rightLedger
    left₁
    left₂
    right₁
    right₂
    leftDerivation
    rightDerivation

/-- The top root exposes scalar compatibility for relation closures. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_smulCongr
    (ledger : TraceCorQRelationLedger)
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure
      ledger
      (TraceCorQQuotientCandidate.smul coefficient left)
      (TraceCorQQuotientCandidate.smul coefficient right) :=
  TraceCorQ.relationClosure_smulCongr
    ledger
    coefficient
    left
    right
    derivation

/-- The top root exposes composition compatibility for relation closures. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_compCongr
    (leftLedger rightLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate)
    (leftDerivation : TraceCorQRelationClosure leftLedger left₁ left₂)
    (rightDerivation : TraceCorQRelationClosure rightLedger right₁ right₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append leftLedger rightLedger)
      (TraceCorQQuotientCandidate.comp left₁ right₁)
      (TraceCorQQuotientCandidate.comp left₂ right₂) :=
  TraceCorQ.relationClosure_compCongr
    leftLedger
    rightLedger
    left₁
    left₂
    right₁
    right₂
    leftDerivation
    rightDerivation

/-- The top root exposes same-formal-sum relation closures. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_sameFormalSum
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (formalSum_eq : left.formalSum = right.formalSum) :
    TraceCorQRelationClosure ledger left right :=
  TraceCorQ.relationClosure_sameFormalSum
    ledger
    left
    right
    formalSum_eq

/-- The top root exposes permuted-formal-sum relation closures. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_permFormalSum
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    TraceCorQRelationClosure ledger left right :=
  TraceCorQ.relationClosure_permFormalSum
    ledger
    left
    right
    formalSum_perm

/-- The top root exposes adjacent opposite-coefficient cancellation. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_cancelAdjacentOpposite
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
  TraceCorQ.relationClosure_cancelAdjacentOpposite
    ledger
    leftContext
    suffix
    coefficient
    generator

/-- The top root exposes adjacent same-generator coefficient combination. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_combineAdjacentSame
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
  TraceCorQ.relationClosure_combineAdjacentSame
    ledger
    leftContext
    suffix
    leftCoefficient
    rightCoefficient
    generator

end AnalyticMotives
end LFunctions
end Boundary
