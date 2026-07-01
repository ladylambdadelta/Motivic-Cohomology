import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Transport.Owner

/-!
# Normalized relation-closure operations

This file owns derived relation-closure operations with normalized ledger
indices.

The underlying derivations still come from the pre-quotient closure syntax.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Add an empty candidate on the left and normalize the resulting ledger. -/
def TraceCorQRelationClosure.addEmptyLeftNormalized
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
  TraceCorQRelationClosure.normalizeEmptyLeftLedger
    (TraceCorQRelationClosure.addEmptyLeft
      ledger
      left
      right
      derivation)

/-- Add an empty candidate on the right and normalize the resulting ledger. -/
def TraceCorQRelationClosure.addEmptyRightNormalized
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
  TraceCorQRelationClosure.normalizeEmptyRightLedger
    (TraceCorQRelationClosure.addEmptyRight
      ledger
      left
      right
      derivation)

end AnalyticMotives
end LFunctions
end Boundary
