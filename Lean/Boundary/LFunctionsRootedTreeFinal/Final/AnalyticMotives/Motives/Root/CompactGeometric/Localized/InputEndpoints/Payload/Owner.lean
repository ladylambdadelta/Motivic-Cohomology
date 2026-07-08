import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Payload.Owner

/-!
# Motive-root payload wrappers for localization-input endpoint morphisms

This file mirrors the endpoint payload facts for compact-generator morphisms
attached to localization inputs under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root input generator hom source rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceLocalizationInput.generatorHom_sourceImportedRectangles
    input

/-- Motive-root input generator hom target rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceLocalizationInput.generatorHom_targetImportedRectangles
    input

/-- Motive-root input generator hom source rectangle count is the input source count. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  TraceLocalizationInput.generatorHom_sourceImportedRectangleCount
    input

/-- Motive-root input generator hom target rectangle count is the input target count. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  TraceLocalizationInput.generatorHom_targetImportedRectangleCount
    input

/-- Motive-root input generator hom source bookkeeping count is the input source count. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.generatorHom_sourceTraceBookkeepingCount
    input

/-- Motive-root input generator hom target bookkeeping count is the input target count. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.generatorHom.targetTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.generatorHom_targetTraceBookkeepingCount
    input

/-- Motive-root input generator hom source rewrite count is the input source count. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  TraceLocalizationInput.generatorHom_sourceRewriteStepCount
    input

/-- Motive-root input generator hom target rewrite count is the input target count. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    input.generatorHom.targetRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  TraceLocalizationInput.generatorHom_targetRewriteStepCount
    input

/-- Motive-root input generator hom source rectangle count is a list length. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceLocalizationInput.generatorHom_sourceImportedRectangleCount_eq_length
    input

/-- Motive-root input generator hom target rectangle count is a list length. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceLocalizationInput.generatorHom_targetImportedRectangleCount_eq_length
    input

end AnalyticMotives
end LFunctions
end Boundary
