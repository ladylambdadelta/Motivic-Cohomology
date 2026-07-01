import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Algebra.Owner

/-!
# Transport for relation-closure derivations

This file owns explicit equality transport for finite relation-closure
derivations.

The transport is only along equality of relation ledgers.  It is a bookkeeping
operation needed before a quotient construction can use normalized ledger
forms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Transport a relation-closure derivation along an equality of ledgers. -/
def TraceCorQRelationClosure.transportLedger
    {sourceLedger targetLedger : TraceCorQRelationLedger}
    {left right : TraceCorQQuotientCandidate}
    (ledger_eq : sourceLedger = targetLedger)
    (derivation :
      TraceCorQRelationClosure sourceLedger left right) :
    TraceCorQRelationClosure targetLedger left right :=
  match ledger_eq with
  | rfl => derivation

/-- Transporting along reflexive ledger equality leaves a derivation unchanged. -/
theorem TraceCorQRelationClosure.transportLedger_rfl
    {ledger : TraceCorQRelationLedger}
    {left right : TraceCorQQuotientCandidate}
    (derivation :
      TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure.transportLedger
      rfl
      derivation =
      derivation :=
  rfl

/-- Transport a relation-closure derivation along endpoint equalities. -/
def TraceCorQRelationClosure.transportEndpoints
    {ledger : TraceCorQRelationLedger}
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (derivation :
      TraceCorQRelationClosure ledger sourceLeft sourceRight) :
    TraceCorQRelationClosure ledger targetLeft targetRight :=
  match left_eq, right_eq with
  | rfl, rfl => derivation

/-- Transporting endpoints along reflexive equalities leaves a derivation unchanged. -/
theorem TraceCorQRelationClosure.transportEndpoints_rfl
    {ledger : TraceCorQRelationLedger}
    {left right : TraceCorQQuotientCandidate}
    (derivation :
      TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure.transportEndpoints
      rfl
      rfl
      derivation =
      derivation :=
  rfl

/-- Normalize a derivation whose ledger has an empty ledger appended on the left. -/
def TraceCorQRelationClosure.normalizeEmptyLeftLedger
    {ledger : TraceCorQRelationLedger}
    {left right : TraceCorQQuotientCandidate}
    (derivation :
      TraceCorQRelationClosure
        (TraceCorQRelationLedger.append
          TraceCorQRelationLedger.empty
          ledger)
        left
        right) :
    TraceCorQRelationClosure ledger left right :=
  TraceCorQRelationClosure.transportLedger
    (TraceCorQRelationLedger.empty_append ledger)
    derivation

/-- Normalize a derivation whose ledger has an empty ledger appended on the right. -/
def TraceCorQRelationClosure.normalizeEmptyRightLedger
    {ledger : TraceCorQRelationLedger}
    {left right : TraceCorQQuotientCandidate}
    (derivation :
      TraceCorQRelationClosure
        (TraceCorQRelationLedger.append
          ledger
          TraceCorQRelationLedger.empty)
        left
        right) :
    TraceCorQRelationClosure ledger left right :=
  TraceCorQRelationClosure.transportLedger
    (TraceCorQRelationLedger.append_empty ledger)
    derivation

end AnalyticMotives
end LFunctions
end Boundary
