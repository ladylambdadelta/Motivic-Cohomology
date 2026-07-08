import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Public.Algebra.Owner

/-!
# Top-root algebraic relation-closure helpers

This file exposes concrete empty-ledger and empty-addition relation-closure
helpers through the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes empty-ledger reflexivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_emptyRefl
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure
      TraceCorQRelationLedger.empty
      candidate
      candidate :=
  TraceCorQ.relationClosure_emptyRefl
    candidate

/-- The top root exposes additive reflexivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_addRefl
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure
      TraceCorQRelationLedger.empty
      (TraceCorQQuotientCandidate.add left right)
      (TraceCorQQuotientCandidate.add left right) :=
  TraceCorQ.relationClosure_addRefl
    left
    right

/-- The top root exposes adding an empty candidate on the left. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_addEmptyLeft
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        TraceCorQRelationLedger.empty
        ledger)
      (TraceCorQQuotientCandidate.add
        TraceCorQQuotientCandidate.empty
        left)
      (TraceCorQQuotientCandidate.add
        TraceCorQQuotientCandidate.empty
        right) :=
  TraceCorQ.relationClosure_addEmptyLeft
    ledger
    left
    right
    derivation

/-- The top root exposes adding an empty candidate on the right. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_addEmptyRight
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        ledger
        TraceCorQRelationLedger.empty)
      (TraceCorQQuotientCandidate.add
        left
        TraceCorQQuotientCandidate.empty)
      (TraceCorQQuotientCandidate.add
        right
        TraceCorQQuotientCandidate.empty) :=
  TraceCorQ.relationClosure_addEmptyRight
    ledger
    left
    right
    derivation

/-- The top root exposes symmetry of empty-ledger reflexivity. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_emptyReflSymm
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure
      TraceCorQRelationLedger.empty
      candidate
      candidate :=
  TraceCorQ.relationClosure_emptyReflSymm
    candidate

/-- The top root exposes normalized empty-left addition. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_addEmptyLeftNormalized
    {ledger : TraceCorQRelationLedger}
    {left right : TraceCorQQuotientCandidate}
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure
      ledger
      (TraceCorQQuotientCandidate.add
        TraceCorQQuotientCandidate.empty
        left)
      (TraceCorQQuotientCandidate.add
        TraceCorQQuotientCandidate.empty
        right) :=
  TraceCorQ.relationClosure_addEmptyLeftNormalized
    derivation

/-- The top root exposes normalized empty-right addition. -/
def AnalyticMotivesRoot.traceCorQRelationClosure_addEmptyRightNormalized
    {ledger : TraceCorQRelationLedger}
    {left right : TraceCorQQuotientCandidate}
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure
      ledger
      (TraceCorQQuotientCandidate.add
        left
        TraceCorQQuotientCandidate.empty)
      (TraceCorQQuotientCandidate.add
        right
        TraceCorQQuotientCandidate.empty) :=
  TraceCorQ.relationClosure_addEmptyRightNormalized
    derivation

end AnalyticMotives
end LFunctions
end Boundary
