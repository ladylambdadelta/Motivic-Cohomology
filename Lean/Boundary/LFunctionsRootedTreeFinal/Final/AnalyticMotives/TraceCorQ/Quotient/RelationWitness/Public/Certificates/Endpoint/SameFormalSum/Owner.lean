import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Endpoint.Owner

/-!
# Public same-formal-sum endpoint certificate facts

This file exposes certificate payload laws for same-formal-sum relation
witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes the supplied certificate ledger for same-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_sameFormalSum_certificateLedger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).certificateLedger =
      ledger.certificateLedger :=
  TraceCorQRelationWitness.sameFormalSum_certificateLedger
    ledger
    formalSum_eq

/-- The trace-correspondence root exposes the supplied imported count for same-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_sameFormalSum_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).importedRectangleCount =
      ledger.importedRectangleCount :=
  TraceCorQRelationWitness.sameFormalSum_importedRectangleCount
    ledger
    formalSum_eq

/-- The trace-correspondence root exposes the supplied imported rectangles for same-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_sameFormalSum_importedRectangles
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).importedRectangles =
      ledger.importedRectangles :=
  TraceCorQRelationWitness.sameFormalSum_importedRectangles
    ledger
    formalSum_eq

/-- The trace-correspondence root exposes the supplied bookkeeping count for same-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_sameFormalSum_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  TraceCorQRelationWitness.sameFormalSum_traceBookkeepingCount
    ledger
    formalSum_eq

/-- The trace-correspondence root exposes the supplied rewrite-step count for same-formal-sum witnesses. -/
theorem TraceCorQ.relationWitness_sameFormalSum_rewriteStepCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).rewriteStepCount =
      ledger.rewriteStepCount :=
  TraceCorQRelationWitness.sameFormalSum_rewriteStepCount
    ledger
    formalSum_eq

end AnalyticMotives
end LFunctions
end Boundary
