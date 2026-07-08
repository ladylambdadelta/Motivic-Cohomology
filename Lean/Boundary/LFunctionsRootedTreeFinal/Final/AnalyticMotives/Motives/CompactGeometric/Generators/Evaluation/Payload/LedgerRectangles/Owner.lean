import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.LedgerCounts.Owner

/-!
# Ledger rectangle lists for compact-generator evaluation payloads

This file records that the imported-rectangle payload at a compact-generator
evaluation point is exactly the imported-rectangle list of its certificate
ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Evaluation-point imported rectangles are the certificate-ledger rectangle list. -/
theorem TraceAnalyticGeometricGenerator.evaluationImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
    generator

end AnalyticMotives
end LFunctions
end Boundary
