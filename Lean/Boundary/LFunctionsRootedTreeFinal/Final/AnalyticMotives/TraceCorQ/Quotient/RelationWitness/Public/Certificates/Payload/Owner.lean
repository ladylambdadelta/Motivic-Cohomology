import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Payload.Owner

/-!
# Public relation-witness certificate payload projections

This file exposes direct certificate-ledger payload projections for relation
witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes relation-witness imported counts as certificate-ledger counts. -/
theorem TraceCorQ.relationWitness_importedRectangleCount_eq_certificateLedger_count
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangleCount =
      witness.certificateLedger.importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_certificateLedger_count
    witness

/-- The trace-correspondence root exposes relation-witness imported rectangles as certificate-ledger rectangles. -/
theorem TraceCorQ.relationWitness_importedRectangles_eq_certificateLedger_rectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangles =
      witness.certificateLedger.importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_certificateLedger_rectangles
    witness

/-- The trace-correspondence root exposes relation-witness bookkeeping counts as certificate-ledger counts. -/
theorem TraceCorQ.relationWitness_traceBookkeepingCount_eq_certificateLedger_count
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.traceBookkeepingCount =
      witness.certificateLedger.traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_certificateLedger_count
    witness

/-- The trace-correspondence root exposes relation-witness rewrite-step counts as certificate-ledger counts. -/
theorem TraceCorQ.relationWitness_rewriteStepCount_eq_certificateLedger_count
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.rewriteStepCount =
      witness.certificateLedger.rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_certificateLedger_count
    witness

end AnalyticMotives
end LFunctions
end Boundary
