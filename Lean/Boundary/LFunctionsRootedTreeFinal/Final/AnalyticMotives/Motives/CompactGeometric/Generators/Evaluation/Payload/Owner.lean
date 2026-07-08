import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Payload.Owner

/-!
# Payload at compact-generator evaluation points

Evaluation does not add a canonical payload to an arbitrary module of sections.
The canonical analytic payload is the imported finite-rectangle payload of the
compact generator used as the evaluation point.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Imported rectangles carried by the evaluation point. -/
def TraceAnalyticGeometricGenerator.evaluationImportedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  generator.importedRectangles

/-- Imported-rectangle count carried by the evaluation point. -/
def TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    Nat :=
  generator.importedRectangleCount

/-- Trace-bookkeeping count carried by the evaluation point. -/
def TraceAnalyticGeometricGenerator.evaluationTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    Nat :=
  generator.traceBookkeepingCount

/-- Rewrite-step count carried by the evaluation point. -/
def TraceAnalyticGeometricGenerator.evaluationRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    Nat :=
  generator.rewriteStepCount

/-- Evaluation-point imported count is counted by its rectangle list. -/
theorem TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.evaluationImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_length_importedRectangles
    generator

/-- Evaluation-point rectangles are the rectangles of the underlying trace object. -/
theorem TraceAnalyticGeometricGenerator.evaluationImportedRectangles_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      generator.traceObject.importedRectangles :=
  rfl

/-- Evaluation-point count is the count of the underlying trace object. -/
theorem TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.traceObject.importedRectangleCount :=
  rfl

/-- Evaluation-point bookkeeping count is the count of the underlying trace object. -/
theorem TraceAnalyticGeometricGenerator.evaluationTraceBookkeepingCount_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      generator.traceObject.traceBookkeepingCount :=
  rfl

/-- Evaluation-point rewrite-step count is the count of the underlying trace object. -/
theorem TraceAnalyticGeometricGenerator.evaluationRewriteStepCount_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      generator.traceObject.rewriteStepCount :=
  rfl

/-- Evaluation-point rectangles agree with the forgetful functor object payload. -/
theorem TraceAnalyticGeometricGenerator.evaluationImportedRectangles_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).importedRectangles :=
  rfl

/-- Evaluation-point count agrees with the forgetful functor object payload count. -/
theorem TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).importedRectangleCount :=
  rfl

/-- Evaluation-point bookkeeping count agrees with the forgetful functor object payload count. -/
theorem TraceAnalyticGeometricGenerator.evaluationTraceBookkeepingCount_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).traceBookkeepingCount :=
  rfl

/-- Evaluation-point rewrite-step count agrees with the forgetful functor object payload count. -/
theorem TraceAnalyticGeometricGenerator.evaluationRewriteStepCount_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj
        generator).rewriteStepCount :=
  rfl

/-- Sections over a compact generator are sections over the evaluation trace object. -/
theorem TraceAnalyticGeometricGenerator.sections_eq_evaluation_traceObject
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.sections presheaf =
      presheaf.sections
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  rfl

/-- Representable evaluation uses the source and target generator endpoint payloads. -/
theorem TraceAnalyticGeometricGenerator.representable_sections_source_payload
    (source target : TraceAnalyticGeometricGenerator) :
    source.evaluationImportedRectangles =
      source.importedRectangles :=
  rfl

/-- Representable evaluation target payload is the represented generator payload. -/
theorem TraceAnalyticGeometricGenerator.representable_sections_target_payload
    (source target : TraceAnalyticGeometricGenerator) :
    target.evaluationImportedRectangles =
      target.importedRectangles :=
  rfl

/-- Representable source evaluation bookkeeping is the source generator bookkeeping. -/
theorem TraceAnalyticGeometricGenerator.representable_sections_source_traceBookkeepingPayload
    (source target : TraceAnalyticGeometricGenerator) :
    source.evaluationTraceBookkeepingCount =
      source.traceBookkeepingCount :=
  rfl

/-- Representable target evaluation bookkeeping is the target generator bookkeeping. -/
theorem TraceAnalyticGeometricGenerator.representable_sections_target_traceBookkeepingPayload
    (source target : TraceAnalyticGeometricGenerator) :
    target.evaluationTraceBookkeepingCount =
      target.traceBookkeepingCount :=
  rfl

/-- Representable source evaluation rewrite count is the source generator rewrite count. -/
theorem TraceAnalyticGeometricGenerator.representable_sections_source_rewriteStepPayload
    (source target : TraceAnalyticGeometricGenerator) :
    source.evaluationRewriteStepCount =
      source.rewriteStepCount :=
  rfl

/-- Representable target evaluation rewrite count is the target generator rewrite count. -/
theorem TraceAnalyticGeometricGenerator.representable_sections_target_rewriteStepPayload
    (source target : TraceAnalyticGeometricGenerator) :
    target.evaluationRewriteStepCount =
      target.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
