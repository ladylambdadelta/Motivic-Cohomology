import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.Owner

/-!
# Ledger counts for compact-generator evaluation payloads

This file records that counts carried by a compact-generator evaluation point
are counted by the certificate ledger of that generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Evaluation-point imported count is counted by the certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
    generator

/-- Evaluation-point bookkeeping count is counted by the certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.evaluationTraceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger
    generator

/-- Evaluation-point rewrite-step count is counted by the certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.evaluationRewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger
    generator

end AnalyticMotives
end LFunctions
end Boundary
