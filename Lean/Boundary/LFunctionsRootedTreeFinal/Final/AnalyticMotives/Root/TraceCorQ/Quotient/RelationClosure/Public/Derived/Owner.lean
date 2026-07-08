import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Public.Derived.Owner

/-!
# Top-root derived relation-closure operations

This file exposes the concrete three-step transitivity and three-term
additivity operations through the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes left-associated three-step transitivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_transLeftAssociated
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
  TraceCorQ.relationClosure_transLeftAssociated
    firstLedger secondLedger thirdLedger
    firstCandidate secondCandidate thirdCandidate fourthCandidate
    first second third

/-- The top root exposes right-associated three-step transitivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_transRightAssociated
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
  TraceCorQ.relationClosure_transRightAssociated
    firstLedger secondLedger thirdLedger
    firstCandidate secondCandidate thirdCandidate fourthCandidate
    first second third

/-- The top root exposes normalized three-step transitivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_transLeftAssociatedNormalized
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
  TraceCorQ.relationClosure_transLeftAssociatedNormalized
    firstLedger secondLedger thirdLedger
    firstCandidate secondCandidate thirdCandidate fourthCandidate
    first second third

/-- The top root exposes left-associated three-term additivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_addThreeLeftAssociated
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
  TraceCorQ.relationClosure_addThreeLeftAssociated
    firstLedger secondLedger thirdLedger
    leftOne leftTwo rightOne rightTwo tailOne tailTwo
    first second third

/-- The top root exposes right-associated three-term additivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_addThreeRightAssociated
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
  TraceCorQ.relationClosure_addThreeRightAssociated
    firstLedger secondLedger thirdLedger
    leftOne leftTwo rightOne rightTwo tailOne tailTwo
    first second third

/-- The top root exposes normalized three-term additivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_addThreeLeftAssociatedNormalized
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
  TraceCorQ.relationClosure_addThreeLeftAssociatedNormalized
    firstLedger secondLedger thirdLedger
    leftOne leftTwo rightOne rightTwo tailOne tailTwo
    first second third

end AnalyticMotives
end LFunctions
end Boundary
