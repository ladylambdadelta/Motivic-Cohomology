import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Pullback.Owner

/-!
# Motive-root compact evaluation

This file collects motive-root facades for compact-generator evaluation payloads
and pullback evaluation endpoint payloads.  The aggregate surface records the
evaluation payload and the underlying trace object used by sections.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root aggregate evaluation rectangles are the certificate-ledger rectangles. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationSummary_importedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangles_eq_certificateLedger_root
    generator

/-- Motive-root aggregate evaluation imported-rectangle count is the certificate-ledger count. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationSummary_importedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_certificateLedger_root
    generator

/-- Motive-root aggregate evaluation imported-rectangle count is the rectangle-list length. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationSummary_importedRectangleCount_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.evaluationImportedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_length
    generator

/-- Motive-root aggregate evaluation bookkeeping is the certificate-ledger count. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationSummary_traceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGenerator_evaluationTraceBookkeepingCount_eq_certificateLedger_root
    generator

/-- Motive-root aggregate evaluation rewrite steps are the certificate-ledger count. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationSummary_rewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGenerator_evaluationRewriteStepCount_eq_certificateLedger_root
    generator

/-- Motive-root aggregate sections are evaluated over the forgetful trace object. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationSummary_sections_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.sections presheaf =
      presheaf.sections
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  TraceAnalyticMotive.compactGenerator_sections_eq_evaluation_traceObject
    generator
    presheaf

end AnalyticMotives
end LFunctions
end Boundary
