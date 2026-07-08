import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner

/-!
# Payload of localization-input compact-generator endpoint morphisms

This file specializes compact-generator morphism endpoint payloads to the
generator morphism attached to a concrete localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source endpoint rectangles of an input generator hom are the input source rectangles. -/
theorem TraceLocalizationInput.generatorHom_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangles =
      input.sourceObject.importedRectangles :=
  rfl

/-- The target endpoint rectangles of an input generator hom are the input target rectangles. -/
theorem TraceLocalizationInput.generatorHom_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangles =
      input.targetObject.importedRectangles :=
  rfl

/-- The source endpoint count of an input generator hom is the input source count. -/
theorem TraceLocalizationInput.generatorHom_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  rfl

/-- The target endpoint count of an input generator hom is the input target count. -/
theorem TraceLocalizationInput.generatorHom_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  rfl

/-- The source endpoint bookkeeping count of an input generator hom is the input source count. -/
theorem TraceLocalizationInput.generatorHom_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  rfl

/-- The target endpoint bookkeeping count of an input generator hom is the input target count. -/
theorem TraceLocalizationInput.generatorHom_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.generatorHom.targetTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  rfl

/-- The source endpoint rewrite count of an input generator hom is the input source count. -/
theorem TraceLocalizationInput.generatorHom_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  rfl

/-- The target endpoint rewrite count of an input generator hom is the input target count. -/
theorem TraceLocalizationInput.generatorHom_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    input.generatorHom.targetRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  rfl

/-- The source endpoint rectangle count of an input generator hom is a rectangle-list length. -/
theorem TraceLocalizationInput.generatorHom_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_length
    input.generatorHom

/-- The target endpoint rectangle count of an input generator hom is a rectangle-list length. -/
theorem TraceLocalizationInput.generatorHom_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_length
    input.generatorHom

end AnalyticMotives
end LFunctions
end Boundary
