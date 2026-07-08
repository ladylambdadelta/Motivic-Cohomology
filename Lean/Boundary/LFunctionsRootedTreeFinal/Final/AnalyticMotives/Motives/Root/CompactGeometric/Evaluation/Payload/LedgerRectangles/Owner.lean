import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.LedgerRectangles.Owner

/-!
# Motive-root compact evaluation ledger rectangles

This file exposes the certificate-ledger rectangle list carried by a compact
generator used as an evaluation point.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Evaluation-point imported rectangles are the certificate-ledger rectangle list. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationImportedRectangles_eq_certificateLedger_root
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangles_eq_certificateLedger
    generator

end AnalyticMotives
end LFunctions
end Boundary
