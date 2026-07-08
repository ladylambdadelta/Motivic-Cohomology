import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Payload.Owner

/-!
# Top-root compact evaluation payloads

This file exposes the finite-rectangle and trace-calculus payload carried by a
compact generator used as an evaluation point.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Evaluation-point imported count is counted by its rectangle list. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationImportedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.evaluationImportedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_length
    generator

/-- Evaluation-point rectangles are the underlying trace-object rectangles. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationImportedRectangles_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      generator.traceObject.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangles_eq_traceObject
    generator

/-- Evaluation-point imported count is the underlying trace-object count. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationImportedRectangleCount_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.traceObject.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_traceObject
    generator

/-- Evaluation-point bookkeeping count is the underlying trace-object count. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationTraceBookkeepingCount_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      generator.traceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGenerator_evaluationTraceBookkeepingCount_eq_traceObject
    generator

/-- Evaluation-point rewrite count is the underlying trace-object count. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationRewriteStepCount_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      generator.traceObject.rewriteStepCount :=
  TraceAnalyticMotive.compactGenerator_evaluationRewriteStepCount_eq_traceObject
    generator

/-- Evaluation-point rectangles agree with the compact generator forgetful object. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationImportedRectangles_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).importedRectangles :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangles_eq_forgetful_obj
    generator

/-- Evaluation-point imported count agrees with the compact generator forgetful object. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationImportedRectangleCount_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_forgetful_obj
    generator

/-- Evaluation-point bookkeeping count agrees with the compact generator forgetful object. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationTraceBookkeepingCount_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).traceBookkeepingCount :=
  TraceAnalyticMotive.compactGenerator_evaluationTraceBookkeepingCount_eq_forgetful_obj
    generator

/-- Evaluation-point rewrite count agrees with the compact generator forgetful object. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluationRewriteStepCount_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).rewriteStepCount :=
  TraceAnalyticMotive.compactGenerator_evaluationRewriteStepCount_eq_forgetful_obj
    generator

/-- Sections over a compact generator are sections over its evaluation trace object. -/
theorem AnalyticMotivesRoot.compactGenerator_sections_eq_evaluation_traceObject
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
