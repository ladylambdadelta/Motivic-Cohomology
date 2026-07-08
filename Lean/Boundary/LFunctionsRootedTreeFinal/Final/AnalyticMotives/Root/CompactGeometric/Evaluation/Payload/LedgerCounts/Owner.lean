import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Payload.LedgerCounts.Owner

/-!
# Top-root compact evaluation ledger counts

This file exposes certificate-ledger counts carried by a compact generator used
as an evaluation point.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Evaluation-point imported count is counted by the certificate ledger. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationImportedRectangleCount_eq_certificateLedger_root
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_certificateLedger_root
    generator

/-- Evaluation-point bookkeeping count is counted by the certificate ledger. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationTraceBookkeepingCount_eq_certificateLedger_root
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGenerator_evaluationTraceBookkeepingCount_eq_certificateLedger_root
    generator

/-- Evaluation-point rewrite-step count is counted by the certificate ledger. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationRewriteStepCount_eq_certificateLedger_root
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGenerator_evaluationRewriteStepCount_eq_certificateLedger_root
    generator

end AnalyticMotives
end LFunctions
end Boundary
