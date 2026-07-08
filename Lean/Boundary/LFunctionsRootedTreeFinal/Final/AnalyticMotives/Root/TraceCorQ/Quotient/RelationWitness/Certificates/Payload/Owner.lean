import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Certificates.Payload.Owner

/-!
# Top-root relation-witness certificate payload projections

This file exposes direct projections from a relation witness's analytic
certificate ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes relation-witness imported counts as certificate-ledger counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_importedRectangleCount_eq_certificateLedger_count
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangleCount =
      witness.certificateLedger.importedRectangleCount :=
  TraceCorQ.relationWitness_importedRectangleCount_eq_certificateLedger_count
    witness

/-- The top root exposes relation-witness imported rectangles as certificate-ledger rectangles. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_importedRectangles_eq_certificateLedger_rectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangles =
      witness.certificateLedger.importedRectangles :=
  TraceCorQ.relationWitness_importedRectangles_eq_certificateLedger_rectangles
    witness

/-- The top root exposes relation-witness bookkeeping counts as certificate-ledger counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_traceBookkeepingCount_eq_certificateLedger_count
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.traceBookkeepingCount =
      witness.certificateLedger.traceBookkeepingCount :=
  TraceCorQ.relationWitness_traceBookkeepingCount_eq_certificateLedger_count
    witness

/-- The top root exposes relation-witness rewrite-step counts as certificate-ledger counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitness_rewriteStepCount_eq_certificateLedger_count
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.rewriteStepCount =
      witness.certificateLedger.rewriteStepCount :=
  TraceCorQ.relationWitness_rewriteStepCount_eq_certificateLedger_count
    witness

end AnalyticMotives
end LFunctions
end Boundary
