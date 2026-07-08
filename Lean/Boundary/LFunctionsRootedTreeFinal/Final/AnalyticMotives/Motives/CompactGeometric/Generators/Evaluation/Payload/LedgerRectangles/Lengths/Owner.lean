import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.LedgerRectangles.Owner

/-!
# Lengths of compact-generator evaluation ledger rectangle lists

This file connects evaluation-point certificate-ledger rectangle-list formulas
to evaluation-point imported-rectangle count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The evaluation-point certificate-ledger rectangle list has the evaluation-point imported count. -/
theorem TraceAnalyticGeometricGenerator.evaluation_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.certificateLedger.importedRectangleCount =
      generator.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_certificateLedger
        generator))
    (Eq.trans
      (TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_length
        generator)
      (congrArg
        List.length
        (TraceAnalyticGeometricGenerator.evaluationImportedRectangles_eq_certificateLedger
          generator)))

end AnalyticMotives
end LFunctions
end Boundary
