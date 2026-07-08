import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationClosure.Public.Owner

/-!
# Top-root TraceCorQ relation-closure surface

This file aggregates the top-root constructor, algebraic, and derived
relation-closure operations for quotient candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Relation-closure aggregate: reflexivity derivation. -/
def AnalyticMotivesRoot.traceCorQRelationClosureSummary_refl
    (ledger : TraceCorQRelationLedger)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure ledger candidate candidate :=
  AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_refl
    ledger
    candidate

/-- Relation-closure aggregate: symmetry derivation. -/
def AnalyticMotivesRoot.traceCorQRelationClosureSummary_symm
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure ledger right left :=
  AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_symm
    ledger
    left
    right
    derivation

/-- Relation-closure aggregate: transitivity appends relation ledgers. -/
def AnalyticMotivesRoot.traceCorQRelationClosureSummary_trans
    (firstLedger secondLedger : TraceCorQRelationLedger)
    (left middle right : TraceCorQQuotientCandidate)
    (first : TraceCorQRelationClosure firstLedger left middle)
    (second : TraceCorQRelationClosure secondLedger middle right) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append firstLedger secondLedger)
      left
      right :=
  AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_trans
    firstLedger
    secondLedger
    left
    middle
    right
    first
    second

/-- Relation-closure aggregate: additive congruence appends relation ledgers. -/
def AnalyticMotivesRoot.traceCorQRelationClosureSummary_addCongr
    (leftLedger rightLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate)
    (leftDerivation : TraceCorQRelationClosure leftLedger left₁ left₂)
    (rightDerivation : TraceCorQRelationClosure rightLedger right₁ right₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append leftLedger rightLedger)
      (TraceCorQQuotientCandidate.add left₁ right₁)
      (TraceCorQQuotientCandidate.add left₂ right₂) :=
  AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_addCongr
    leftLedger
    rightLedger
    left₁
    left₂
    right₁
    right₂
    leftDerivation
    rightDerivation

/-- Relation-closure aggregate: normalized three-step transitivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosureSummary_transLeftAssociatedNormalized
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
  AnalyticMotivesRoot.traceCorQRelationClosure_publicSummary_transLeftAssociatedNormalized
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
