import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Facade.UnstablePayload.Owner

/-!
# Top-root compact-geometric evaluation payload facade
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes compact evaluation rectangle payload. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangles_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact evaluation imported-rectangle counts. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact evaluation ledger rectangle lengths. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluation_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.certificateLedger.importedRectangleCount =
      generator.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_evaluation_certificateLedgerRectangles_length
    generator

/-- The analytic-motives root exposes compact evaluation bookkeeping counts. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationTraceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGenerator_evaluationTraceBookkeepingCount_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact evaluation rewrite-step counts. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationRewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGenerator_evaluationRewriteStepCount_eq_certificateLedger
    generator

end AnalyticMotives
end LFunctions
end Boundary
