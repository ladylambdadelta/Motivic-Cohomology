import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Pullback.Owner

/-!
# Top-root compact evaluation

This file collects public root facades for compact-generator evaluation payloads
and pullback evaluation endpoint payloads.  The aggregate surface records the
evaluation payload and the underlying trace object used by sections.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root aggregate evaluation rectangles are the certificate-ledger rectangles. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationSummary_importedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_evaluationSummary_importedRectangles
    generator

/-- Top-root aggregate evaluation imported-rectangle count is the certificate-ledger count. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationSummary_importedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_evaluationSummary_importedRectangleCount
    generator

/-- Top-root aggregate evaluation imported-rectangle count is the rectangle-list length. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationSummary_importedRectangleCount_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.evaluationImportedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_evaluationSummary_importedRectangleCount_length
    generator

/-- Top-root aggregate evaluation bookkeeping is the certificate-ledger count. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationSummary_traceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGenerator_evaluationSummary_traceBookkeepingCount
    generator

/-- Top-root aggregate evaluation rewrite steps are the certificate-ledger count. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationSummary_rewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGenerator_evaluationSummary_rewriteStepCount
    generator

/-- Top-root aggregate sections are evaluated over the forgetful trace object. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationSummary_sections_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.sections presheaf =
      presheaf.sections
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  TraceAnalyticMotive.compactGenerator_evaluationSummary_sections_eq_forgetful_obj
    generator
    presheaf

end AnalyticMotives
end LFunctions
end Boundary
