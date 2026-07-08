import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Endpoint.Owner

/-!
# Public permuted-formal-sum endpoint certificate facts

This file exposes certificate payload laws for permuted-formal-sum relation
witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes the supplied certificate ledger for permuted-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_permFormalSum_certificateLedger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).certificateLedger =
      ledger.certificateLedger :=
  TraceCorQRelationWitness.permFormalSum_certificateLedger
    ledger
    formalSum_perm

/-- The trace-correspondence root exposes the supplied imported count for permuted-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_permFormalSum_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).importedRectangleCount =
      ledger.importedRectangleCount :=
  TraceCorQRelationWitness.permFormalSum_importedRectangleCount
    ledger
    formalSum_perm

/-- The trace-correspondence root exposes the supplied imported rectangles for permuted-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_permFormalSum_importedRectangles
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).importedRectangles =
      ledger.importedRectangles :=
  TraceCorQRelationWitness.permFormalSum_importedRectangles
    ledger
    formalSum_perm

/-- The trace-correspondence root exposes the supplied bookkeeping count for permuted-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_permFormalSum_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  TraceCorQRelationWitness.permFormalSum_traceBookkeepingCount
    ledger
    formalSum_perm

/-- The trace-correspondence root exposes the supplied rewrite-step count for permuted-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_permFormalSum_rewriteStepCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).rewriteStepCount =
      ledger.rewriteStepCount :=
  TraceCorQRelationWitness.permFormalSum_rewriteStepCount
    ledger
    formalSum_perm

end AnalyticMotives
end LFunctions
end Boundary
