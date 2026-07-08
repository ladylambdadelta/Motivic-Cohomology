import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Owner

/-!
# Certificate-payload projections for relation witnesses

This file records direct projections from a relation witness's analytic
certificate ledger.  The base certificate owner relates witnesses to relation
ledgers; this nested owner gives downstream users the certificate-ledger view
without unfolding through that ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A relation witness imports exactly the payload counted by its certificate ledger. -/
theorem TraceCorQRelationWitness.importedRectangleCount_eq_certificateLedger_count
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangleCount =
      witness.certificateLedger.importedRectangleCount :=
  rfl

/-- A relation witness exposes exactly the rectangles extracted from its certificate ledger. -/
theorem TraceCorQRelationWitness.importedRectangles_eq_certificateLedger_rectangles
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangles =
      witness.certificateLedger.importedRectangles :=
  rfl

/-- A relation witness's bookkeeping payload is counted by its certificate ledger. -/
theorem TraceCorQRelationWitness.traceBookkeepingCount_eq_certificateLedger_count
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.traceBookkeepingCount =
      witness.certificateLedger.traceBookkeepingCount :=
  rfl

/-- A relation witness's rewrite-step payload is counted by its certificate ledger. -/
theorem TraceCorQRelationWitness.rewriteStepCount_eq_certificateLedger_count
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.rewriteStepCount =
      witness.certificateLedger.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
