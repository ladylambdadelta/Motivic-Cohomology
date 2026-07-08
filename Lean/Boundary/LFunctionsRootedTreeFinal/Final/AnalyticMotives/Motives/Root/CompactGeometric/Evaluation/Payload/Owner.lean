import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.Owner

/-!
# Motive-root compact evaluation payloads

This file exposes the finite-rectangle and trace-calculus payload carried by a
compact generator used as an evaluation point.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Evaluation-point imported count is counted by its rectangle list. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.evaluationImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_length
    generator

/-- Evaluation-point rectangles are the underlying trace-object rectangles. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationImportedRectangles_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      generator.traceObject.importedRectangles :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangles_eq_traceObject
    generator

/-- Evaluation-point imported count is the underlying trace-object count. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.traceObject.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_traceObject
    generator

/-- Evaluation-point bookkeeping count is the underlying trace-object count. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationTraceBookkeepingCount_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      generator.traceObject.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.evaluationTraceBookkeepingCount_eq_traceObject
    generator

/-- Evaluation-point rewrite count is the underlying trace-object count. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationRewriteStepCount_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      generator.traceObject.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.evaluationRewriteStepCount_eq_traceObject
    generator

/-- Evaluation-point rectangles agree with the compact generator forgetful object. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationImportedRectangles_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).importedRectangles :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangles_eq_forgetful_obj
    generator

/-- Evaluation-point imported count agrees with the compact generator forgetful object. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).importedRectangleCount :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_forgetful_obj
    generator

/-- Evaluation-point bookkeeping count agrees with the compact generator forgetful object. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationTraceBookkeepingCount_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.evaluationTraceBookkeepingCount_eq_forgetful_obj
    generator

/-- Evaluation-point rewrite count agrees with the compact generator forgetful object. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationRewriteStepCount_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).rewriteStepCount :=
  TraceAnalyticGeometricGenerator.evaluationRewriteStepCount_eq_forgetful_obj
    generator

/-- Sections over a compact generator are sections over its evaluation trace object. -/
theorem TraceAnalyticMotive.compactGenerator_sections_eq_evaluation_traceObject
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.sections presheaf =
      presheaf.sections
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  TraceAnalyticGeometricGenerator.sections_eq_evaluation_traceObject
    generator
    presheaf

/-- Representable source evaluation uses the source generator rectangle payload. -/
theorem TraceAnalyticMotive.compactGenerator_representable_sections_source_payload
    (source target : TraceAnalyticGeometricGenerator) :
    source.evaluationImportedRectangles =
      source.importedRectangles :=
  TraceAnalyticGeometricGenerator.representable_sections_source_payload
    source
    target

/-- Representable target evaluation uses the target generator rectangle payload. -/
theorem TraceAnalyticMotive.compactGenerator_representable_sections_target_payload
    (source target : TraceAnalyticGeometricGenerator) :
    target.evaluationImportedRectangles =
      target.importedRectangles :=
  TraceAnalyticGeometricGenerator.representable_sections_target_payload
    source
    target

/-- Representable source evaluation bookkeeping is the source generator bookkeeping. -/
theorem TraceAnalyticMotive.compactGenerator_representable_sections_source_traceBookkeepingPayload
    (source target : TraceAnalyticGeometricGenerator) :
    source.evaluationTraceBookkeepingCount =
      source.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.representable_sections_source_traceBookkeepingPayload
    source
    target

/-- Representable target evaluation bookkeeping is the target generator bookkeeping. -/
theorem TraceAnalyticMotive.compactGenerator_representable_sections_target_traceBookkeepingPayload
    (source target : TraceAnalyticGeometricGenerator) :
    target.evaluationTraceBookkeepingCount =
      target.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.representable_sections_target_traceBookkeepingPayload
    source
    target

/-- Representable source evaluation rewrite count is the source generator rewrite count. -/
theorem TraceAnalyticMotive.compactGenerator_representable_sections_source_rewriteStepPayload
    (source target : TraceAnalyticGeometricGenerator) :
    source.evaluationRewriteStepCount =
      source.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.representable_sections_source_rewriteStepPayload
    source
    target

/-- Representable target evaluation rewrite count is the target generator rewrite count. -/
theorem TraceAnalyticMotive.compactGenerator_representable_sections_target_rewriteStepPayload
    (source target : TraceAnalyticGeometricGenerator) :
    target.evaluationRewriteStepCount =
      target.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.representable_sections_target_rewriteStepPayload
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
