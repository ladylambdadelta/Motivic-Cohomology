import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Derived.Owner

/-!
# Public derived relation-closure operations

This file exposes the concrete three-step transitivity and three-term
additivity operations under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes left-associated three-step transitivity. -/
def TraceCorQ.relationClosure_transLeftAssociated
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
        (TraceCorQRelationLedger.append firstLedger secondLedger)
        thirdLedger)
      firstCandidate
      fourthCandidate :=
  TraceCorQRelationClosure.transLeftAssociated
    firstLedger secondLedger thirdLedger
    firstCandidate secondCandidate thirdCandidate fourthCandidate
    first second third

/-- The trace-correspondence root exposes right-associated three-step transitivity. -/
def TraceCorQ.relationClosure_transRightAssociated
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
  TraceCorQRelationClosure.transRightAssociated
    firstLedger secondLedger thirdLedger
    firstCandidate secondCandidate thirdCandidate fourthCandidate
    first second third

/-- The trace-correspondence root exposes normalized three-step transitivity. -/
def TraceCorQ.relationClosure_transLeftAssociatedNormalized
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
  TraceCorQRelationClosure.transLeftAssociatedNormalized
    firstLedger secondLedger thirdLedger
    firstCandidate secondCandidate thirdCandidate fourthCandidate
    first second third

/-- The trace-correspondence root exposes left-associated three-term additivity. -/
def TraceCorQ.relationClosure_addThreeLeftAssociated
    (firstLedger secondLedger thirdLedger : TraceCorQRelationLedger)
    (leftOne leftTwo rightOne rightTwo tailOne tailTwo :
      TraceCorQQuotientCandidate)
    (first : TraceCorQRelationClosure firstLedger leftOne leftTwo)
    (second : TraceCorQRelationClosure secondLedger rightOne rightTwo)
    (third : TraceCorQRelationClosure thirdLedger tailOne tailTwo) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        (TraceCorQRelationLedger.append firstLedger secondLedger)
        thirdLedger)
      (TraceCorQQuotientCandidate.add
        (TraceCorQQuotientCandidate.add leftOne rightOne)
        tailOne)
      (TraceCorQQuotientCandidate.add
        (TraceCorQQuotientCandidate.add leftTwo rightTwo)
        tailTwo) :=
  TraceCorQRelationClosure.addThreeLeftAssociated
    firstLedger secondLedger thirdLedger
    leftOne leftTwo rightOne rightTwo tailOne tailTwo
    first second third

/-- The trace-correspondence root exposes right-associated three-term additivity. -/
def TraceCorQ.relationClosure_addThreeRightAssociated
    (firstLedger secondLedger thirdLedger : TraceCorQRelationLedger)
    (leftOne leftTwo rightOne rightTwo tailOne tailTwo :
      TraceCorQQuotientCandidate)
    (first : TraceCorQRelationClosure firstLedger leftOne leftTwo)
    (second : TraceCorQRelationClosure secondLedger rightOne rightTwo)
    (third : TraceCorQRelationClosure thirdLedger tailOne tailTwo) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        firstLedger
        (TraceCorQRelationLedger.append secondLedger thirdLedger))
      (TraceCorQQuotientCandidate.add
        leftOne
        (TraceCorQQuotientCandidate.add rightOne tailOne))
      (TraceCorQQuotientCandidate.add
        leftTwo
        (TraceCorQQuotientCandidate.add rightTwo tailTwo)) :=
  TraceCorQRelationClosure.addThreeRightAssociated
    firstLedger secondLedger thirdLedger
    leftOne leftTwo rightOne rightTwo tailOne tailTwo
    first second third

/-- The trace-correspondence root exposes normalized three-term additivity. -/
def TraceCorQ.relationClosure_addThreeLeftAssociatedNormalized
    (firstLedger secondLedger thirdLedger : TraceCorQRelationLedger)
    (leftOne leftTwo rightOne rightTwo tailOne tailTwo :
      TraceCorQQuotientCandidate)
    (first : TraceCorQRelationClosure firstLedger leftOne leftTwo)
    (second : TraceCorQRelationClosure secondLedger rightOne rightTwo)
    (third : TraceCorQRelationClosure thirdLedger tailOne tailTwo) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        firstLedger
        (TraceCorQRelationLedger.append secondLedger thirdLedger))
      (TraceCorQQuotientCandidate.add
        leftOne
        (TraceCorQQuotientCandidate.add rightOne tailOne))
      (TraceCorQQuotientCandidate.add
        leftTwo
        (TraceCorQQuotientCandidate.add rightTwo tailTwo)) :=
  TraceCorQRelationClosure.addThreeLeftAssociatedNormalized
    firstLedger secondLedger thirdLedger
    leftOne leftTwo rightOne rightTwo tailOne tailTwo
    first second third

end AnalyticMotives
end LFunctions
end Boundary
