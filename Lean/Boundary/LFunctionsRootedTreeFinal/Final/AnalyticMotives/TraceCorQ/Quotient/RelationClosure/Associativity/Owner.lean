import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Transport.Owner

/-!
# Associativity for relation-closure transitivity

This file owns explicit associativity-normalized transitivity for finite
relation-closure derivations.

The normalization is done by transporting along the concrete ledger
associativity equality.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Left-associated composition of three relation-closure derivations. -/
def TraceCorQRelationClosure.transLeftAssociated
    (firstLedger secondLedger thirdLedger : TraceCorQRelationLedger)
    (firstCandidate secondCandidate thirdCandidate fourthCandidate :
      TraceCorQQuotientCandidate)
    (first :
      TraceCorQRelationClosure
        firstLedger
        firstCandidate
        secondCandidate)
    (second :
      TraceCorQRelationClosure
        secondLedger
        secondCandidate
        thirdCandidate)
    (third :
      TraceCorQRelationClosure
        thirdLedger
        thirdCandidate
        fourthCandidate) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        (TraceCorQRelationLedger.append firstLedger secondLedger)
        thirdLedger)
      firstCandidate
      fourthCandidate :=
  TraceCorQRelationClosure.transDerivation
    (TraceCorQRelationLedger.append firstLedger secondLedger)
    thirdLedger
    firstCandidate
    thirdCandidate
    fourthCandidate
    (TraceCorQRelationClosure.transDerivation
      firstLedger
      secondLedger
      firstCandidate
      secondCandidate
      thirdCandidate
      first
      second)
    third

/-- Right-associated composition of three relation-closure derivations. -/
def TraceCorQRelationClosure.transRightAssociated
    (firstLedger secondLedger thirdLedger : TraceCorQRelationLedger)
    (firstCandidate secondCandidate thirdCandidate fourthCandidate :
      TraceCorQQuotientCandidate)
    (first :
      TraceCorQRelationClosure
        firstLedger
        firstCandidate
        secondCandidate)
    (second :
      TraceCorQRelationClosure
        secondLedger
        secondCandidate
        thirdCandidate)
    (third :
      TraceCorQRelationClosure
        thirdLedger
        thirdCandidate
        fourthCandidate) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        firstLedger
        (TraceCorQRelationLedger.append secondLedger thirdLedger))
      firstCandidate
      fourthCandidate :=
  TraceCorQRelationClosure.transDerivation
    firstLedger
    (TraceCorQRelationLedger.append secondLedger thirdLedger)
    firstCandidate
    secondCandidate
    fourthCandidate
    first
    (TraceCorQRelationClosure.transDerivation
      secondLedger
      thirdLedger
      secondCandidate
      thirdCandidate
      fourthCandidate
      second
      third)

/-- Left-associated transitivity transported to the right-associated ledger. -/
def TraceCorQRelationClosure.transLeftAssociatedNormalized
    (firstLedger secondLedger thirdLedger : TraceCorQRelationLedger)
    (firstCandidate secondCandidate thirdCandidate fourthCandidate :
      TraceCorQQuotientCandidate)
    (first :
      TraceCorQRelationClosure
        firstLedger
        firstCandidate
        secondCandidate)
    (second :
      TraceCorQRelationClosure
        secondLedger
        secondCandidate
        thirdCandidate)
    (third :
      TraceCorQRelationClosure
        thirdLedger
        thirdCandidate
        fourthCandidate) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        firstLedger
        (TraceCorQRelationLedger.append secondLedger thirdLedger))
      firstCandidate
      fourthCandidate :=
  TraceCorQRelationClosure.transportLedger
    (TraceCorQRelationLedger.append_assoc
      firstLedger
      secondLedger
      thirdLedger)
    (TraceCorQRelationClosure.transLeftAssociated
      firstLedger
      secondLedger
      thirdLedger
      firstCandidate
      secondCandidate
      thirdCandidate
      fourthCandidate
      first
      second
      third)

end AnalyticMotives
end LFunctions
end Boundary
