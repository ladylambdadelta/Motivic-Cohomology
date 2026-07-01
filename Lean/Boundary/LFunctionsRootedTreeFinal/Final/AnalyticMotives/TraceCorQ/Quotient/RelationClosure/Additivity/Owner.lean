import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Associativity.Owner

/-!
# Additivity for relation-closure derivations

This file owns three-term additive compatibility for finite relation-closure
derivations.

Both ledger and candidate parenthesization are normalized explicitly by
transport.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Left-associated additive compatibility for three relation-closure derivations. -/
def TraceCorQRelationClosure.addThreeLeftAssociated
    (firstLedger secondLedger thirdLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ tail₁ tail₂ :
      TraceCorQQuotientCandidate)
    (first :
      TraceCorQRelationClosure firstLedger left₁ left₂)
    (second :
      TraceCorQRelationClosure secondLedger right₁ right₂)
    (third :
      TraceCorQRelationClosure thirdLedger tail₁ tail₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        (TraceCorQRelationLedger.append firstLedger secondLedger)
        thirdLedger)
      (TraceCorQQuotientCandidate.add
        (TraceCorQQuotientCandidate.add left₁ right₁)
        tail₁)
      (TraceCorQQuotientCandidate.add
        (TraceCorQQuotientCandidate.add left₂ right₂)
        tail₂) :=
  TraceCorQRelationClosure.addCongrDerivation
    (TraceCorQRelationLedger.append firstLedger secondLedger)
    thirdLedger
    (TraceCorQQuotientCandidate.add left₁ right₁)
    (TraceCorQQuotientCandidate.add left₂ right₂)
    tail₁
    tail₂
    (TraceCorQRelationClosure.addCongrDerivation
      firstLedger
      secondLedger
      left₁
      left₂
      right₁
      right₂
      first
      second)
    third

/-- Right-associated additive compatibility for three relation-closure derivations. -/
def TraceCorQRelationClosure.addThreeRightAssociated
    (firstLedger secondLedger thirdLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ tail₁ tail₂ :
      TraceCorQQuotientCandidate)
    (first :
      TraceCorQRelationClosure firstLedger left₁ left₂)
    (second :
      TraceCorQRelationClosure secondLedger right₁ right₂)
    (third :
      TraceCorQRelationClosure thirdLedger tail₁ tail₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        firstLedger
        (TraceCorQRelationLedger.append secondLedger thirdLedger))
      (TraceCorQQuotientCandidate.add
        left₁
        (TraceCorQQuotientCandidate.add right₁ tail₁))
      (TraceCorQQuotientCandidate.add
        left₂
        (TraceCorQQuotientCandidate.add right₂ tail₂)) :=
  TraceCorQRelationClosure.addCongrDerivation
    firstLedger
    (TraceCorQRelationLedger.append secondLedger thirdLedger)
    left₁
    left₂
    (TraceCorQQuotientCandidate.add right₁ tail₁)
    (TraceCorQQuotientCandidate.add right₂ tail₂)
    first
    (TraceCorQRelationClosure.addCongrDerivation
      secondLedger
      thirdLedger
      right₁
      right₂
      tail₁
      tail₂
      second
      third)

/--
Left-associated additive compatibility transported to the right-associated
ledger and right-associated candidate endpoints.
-/
def TraceCorQRelationClosure.addThreeLeftAssociatedNormalized
    (firstLedger secondLedger thirdLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ tail₁ tail₂ :
      TraceCorQQuotientCandidate)
    (first :
      TraceCorQRelationClosure firstLedger left₁ left₂)
    (second :
      TraceCorQRelationClosure secondLedger right₁ right₂)
    (third :
      TraceCorQRelationClosure thirdLedger tail₁ tail₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        firstLedger
        (TraceCorQRelationLedger.append secondLedger thirdLedger))
      (TraceCorQQuotientCandidate.add
        left₁
        (TraceCorQQuotientCandidate.add right₁ tail₁))
      (TraceCorQQuotientCandidate.add
        left₂
        (TraceCorQQuotientCandidate.add right₂ tail₂)) :=
  TraceCorQRelationClosure.transportEndpoints
    (TraceCorQQuotientCandidate.add_assoc left₁ right₁ tail₁)
    (TraceCorQQuotientCandidate.add_assoc left₂ right₂ tail₂)
    (TraceCorQRelationClosure.transportLedger
      (TraceCorQRelationLedger.append_assoc
        firstLedger
        secondLedger
        thirdLedger)
      (TraceCorQRelationClosure.addThreeLeftAssociated
        firstLedger
        secondLedger
        thirdLedger
        left₁
        left₂
        right₁
        right₂
        tail₁
        tail₂
        first
        second
        third))

end AnalyticMotives
end LFunctions
end Boundary
