import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Normalized.Owner

/-!
# Public algebraic relation-closure helpers

This file exposes concrete empty-ledger and empty-addition relation-closure
helpers under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes empty-ledger reflexivity. -/
def TraceCorQ.relationClosure_emptyRefl
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure
      TraceCorQRelationLedger.empty
      candidate
      candidate :=
  TraceCorQRelationClosure.emptyRefl
    candidate

/-- The trace-correspondence root exposes additive reflexivity. -/
def TraceCorQ.relationClosure_addRefl
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure
      TraceCorQRelationLedger.empty
      (TraceCorQQuotientCandidate.add left right)
      (TraceCorQQuotientCandidate.add left right) :=
  TraceCorQRelationClosure.addRefl
    left
    right

/-- The trace-correspondence root exposes adding an empty candidate on the left. -/
def TraceCorQ.relationClosure_addEmptyLeft
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
  TraceCorQRelationClosure.addEmptyLeft
    ledger
    left
    right
    derivation

/-- The trace-correspondence root exposes adding an empty candidate on the right. -/
def TraceCorQ.relationClosure_addEmptyRight
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
  TraceCorQRelationClosure.addEmptyRight
    ledger
    left
    right
    derivation

/-- The trace-correspondence root exposes symmetry of empty-ledger reflexivity. -/
def TraceCorQ.relationClosure_emptyReflSymm
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure
      TraceCorQRelationLedger.empty
      candidate
      candidate :=
  TraceCorQRelationClosure.emptyReflSymm
    candidate

/-- The trace-correspondence root exposes normalized empty-left addition. -/
def TraceCorQ.relationClosure_addEmptyLeftNormalized
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
  TraceCorQRelationClosure.addEmptyLeftNormalized
    derivation

/-- The trace-correspondence root exposes normalized empty-right addition. -/
def TraceCorQ.relationClosure_addEmptyRightNormalized
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
  TraceCorQRelationClosure.addEmptyRightNormalized
    derivation

end AnalyticMotives
end LFunctions
end Boundary
