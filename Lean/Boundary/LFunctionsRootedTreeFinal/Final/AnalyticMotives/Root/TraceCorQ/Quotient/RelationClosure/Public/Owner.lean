import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationClosure.Public.Algebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationClosure.Public.Constructors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationClosure.Public.Derived.Owner

/-!
# Top-root public relation-closure surfaces

This file aggregates the top-root public constructor, algebraic, and derived
relation-closure surfaces for quotient candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Relation-closure public aggregate: reflexivity derivation. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_refl
    (ledger : TraceCorQRelationLedger)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure ledger candidate candidate :=
  AnalyticMotivesRoot.traceCorQRelationClosure_refl
    ledger
    candidate

/-- Relation-closure public aggregate: symmetry derivation. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_symm
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure ledger right left :=
  AnalyticMotivesRoot.traceCorQRelationClosure_symm
    ledger
    left
    right
    derivation

/-- Relation-closure public aggregate: transitivity appends relation ledgers. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_trans
    (firstLedger secondLedger : TraceCorQRelationLedger)
    (left middle right : TraceCorQQuotientCandidate)
    (first : TraceCorQRelationClosure firstLedger left middle)
    (second : TraceCorQRelationClosure secondLedger middle right) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append firstLedger secondLedger)
      left
      right :=
  AnalyticMotivesRoot.traceCorQRelationClosure_trans
    firstLedger
    secondLedger
    left
    middle
    right
    first
    second

/-- Relation-closure public aggregate: additive congruence appends relation ledgers. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_addCongr
    (leftLedger rightLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate)
    (leftDerivation : TraceCorQRelationClosure leftLedger left₁ left₂)
    (rightDerivation : TraceCorQRelationClosure rightLedger right₁ right₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append leftLedger rightLedger)
      (TraceCorQQuotientCandidate.add left₁ right₁)
      (TraceCorQQuotientCandidate.add left₂ right₂) :=
  AnalyticMotivesRoot.traceCorQRelationClosure_addCongr
    leftLedger
    rightLedger
    left₁
    left₂
    right₁
    right₂
    leftDerivation
    rightDerivation

/-- Relation-closure public aggregate: scalar congruence preserves the ledger. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_smulCongr
    (ledger : TraceCorQRelationLedger)
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure
      ledger
      (TraceCorQQuotientCandidate.smul coefficient left)
      (TraceCorQQuotientCandidate.smul coefficient right) :=
  AnalyticMotivesRoot.traceCorQRelationClosure_smulCongr
    ledger
    coefficient
    left
    right
    derivation

/-- Relation-closure public aggregate: normalized three-step transitivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_transLeftAssociatedNormalized
    (firstLedger secondLedger thirdLedger : TraceCorQRelationLedger)
    (firstCandidate secondCandidate thirdCandidate fourthCandidate :
      TraceCorQQuotientCandidate)
    (first :
      TraceCorQRelationClosure firstLedger firstCandidate secondCandidate)
    (second :
      TraceCorQRelationClosure secondLedger secondCandidate thirdCandidate)
    (third :
      TraceCorQRelationClosure thirdLedger thirdCandidate fourthCandidate) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        firstLedger
        (TraceCorQRelationLedger.append secondLedger thirdLedger))
      firstCandidate
      fourthCandidate :=
  AnalyticMotivesRoot.traceCorQRelationClosure_transLeftAssociatedNormalized
    firstLedger
    secondLedger
    thirdLedger
    firstCandidate
    secondCandidate
    thirdCandidate
    fourthCandidate
    first
    second
    third

end AnalyticMotives
end LFunctions
end Boundary
