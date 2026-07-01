import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Owner

/-!
# Algebra of relation-closure derivations

This file owns basic derived operations for finite relation-closure
derivations.

These declarations remain pre-quotient: they build derivations, not quotient
classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Empty-ledger reflexivity for a quotient candidate. -/
def TraceCorQRelationClosure.emptyRefl
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure
      TraceCorQRelationLedger.empty
      candidate
      candidate :=
  TraceCorQRelationClosure.reflDerivation
    TraceCorQRelationLedger.empty
    candidate

/-- Additive compatibility of two reflexive derivations. -/
def TraceCorQRelationClosure.addRefl
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure
      TraceCorQRelationLedger.empty
      (TraceCorQQuotientCandidate.add left right)
      (TraceCorQQuotientCandidate.add left right) :=
  TraceCorQRelationClosure.reflDerivation
    TraceCorQRelationLedger.empty
    (TraceCorQQuotientCandidate.add left right)

/-- Add an empty candidate on the left side of a derivation. -/
def TraceCorQRelationClosure.addEmptyLeft
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
  TraceCorQRelationClosure.addCongrDerivation
    TraceCorQRelationLedger.empty
    ledger
    TraceCorQQuotientCandidate.empty
    TraceCorQQuotientCandidate.empty
    left
    right
    (TraceCorQRelationClosure.emptyRefl
      TraceCorQQuotientCandidate.empty)
    derivation

/-- Add an empty candidate on the right side of a derivation. -/
def TraceCorQRelationClosure.addEmptyRight
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
  TraceCorQRelationClosure.addCongrDerivation
    ledger
    TraceCorQRelationLedger.empty
    left
    right
    TraceCorQQuotientCandidate.empty
    TraceCorQQuotientCandidate.empty
    derivation
    (TraceCorQRelationClosure.emptyRefl
      TraceCorQQuotientCandidate.empty)

/-- Symmetry of empty-ledger reflexivity is empty-ledger reflexivity. -/
def TraceCorQRelationClosure.emptyReflSymm
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure
      TraceCorQRelationLedger.empty
      candidate
      candidate :=
  TraceCorQRelationClosure.symmDerivation
    TraceCorQRelationLedger.empty
    candidate
    candidate
    (TraceCorQRelationClosure.emptyRefl candidate)

end AnalyticMotives
end LFunctions
end Boundary
