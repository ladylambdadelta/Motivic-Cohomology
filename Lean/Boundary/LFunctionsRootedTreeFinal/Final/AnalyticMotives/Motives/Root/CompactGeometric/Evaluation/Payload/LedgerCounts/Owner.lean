import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.LedgerCounts.Owner

/-!
# Motive-root compact evaluation ledger counts

This file exposes certificate-ledger counts carried by a compact generator used
as an evaluation point.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Evaluation-point imported count is counted by the certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_certificateLedger_root
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_certificateLedger
    generator

/-- Evaluation-point bookkeeping count is counted by the certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationTraceBookkeepingCount_eq_certificateLedger_root
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.evaluationTraceBookkeepingCount_eq_certificateLedger
    generator

/-- Evaluation-point rewrite-step count is counted by the certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationRewriteStepCount_eq_certificateLedger_root
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.evaluationRewriteStepCount_eq_certificateLedger
    generator

end AnalyticMotives
end LFunctions
end Boundary
