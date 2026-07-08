import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Facade.Evaluation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Owner

/-!
# Motive-root compact-geometric localization-input facade

This file exposes localization-input compact-generator endpoint wrappers under
the `TraceAnalyticMotive` root facade.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compact-geometric root aggregate: localization input source generator is its source object. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_source_traceObject
    (input : TraceLocalizationInput) :
    input.sourceGenerator.traceObject =
      input.sourceObject :=
  TraceAnalyticMotive.localizationInput_sourceGenerator_traceObject
    input

/-- Compact-geometric root aggregate: localization input target generator is its target object. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_target_traceObject
    (input : TraceLocalizationInput) :
    input.targetGenerator.traceObject =
      input.targetObject :=
  TraceAnalyticMotive.localizationInput_targetGenerator_traceObject
    input

/-- Compact-geometric root aggregate: localization input source generator has wrapped localized object. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_source_localizedWordObject
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject input.sourceObject :=
  TraceAnalyticMotive.localizationInput_sourceGenerator_localizedWordObject
    input

/-- Compact-geometric root aggregate: localization input target generator has wrapped localized object. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_target_localizedWordObject
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject input.targetObject :=
  TraceAnalyticMotive.localizationInput_targetGenerator_localizedWordObject
    input

/-- Compact-geometric root aggregate: localization input source generator has source presheaf. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_source_presheaf
    (input : TraceLocalizationInput) :
    input.sourceGenerator.presheaf =
      input.sourcePresheaf :=
  TraceAnalyticMotive.localizationInput_sourceGenerator_presheaf
    input

/-- Compact-geometric root aggregate: localization input target generator has target presheaf. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_target_presheaf
    (input : TraceLocalizationInput) :
    input.targetGenerator.presheaf =
      input.targetPresheaf :=
  TraceAnalyticMotive.localizationInput_targetGenerator_presheaf
    input

/-- Compact-geometric root aggregate: localization input generator hom has the input trace hom. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_traceHom
    (input : TraceLocalizationInput) :
    input.generatorHom.traceHom =
      input.traceHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_traceHom
    input

/-- Compact-geometric root aggregate: localization input generator hom induces the input map. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_representableMap
    (input : TraceLocalizationInput) :
    input.generatorHom.representableMap =
      input.map :=
  TraceAnalyticMotive.localizationInput_generatorHom_representableMap
    input

/-- Compact-geometric root aggregate: input generator hom source rectangles are input source rectangles. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceAnalyticMotive.localizationInput_generatorHom_sourceImportedRectangles
    input

/-- Compact-geometric root aggregate: input generator hom target rectangles are input target rectangles. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceAnalyticMotive.localizationInput_generatorHom_targetImportedRectangles
    input

/-- Compact-geometric root aggregate: input generator hom source rectangle count is a list length. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.localizationInput_generatorHom_sourceImportedRectangleCount_eq_length
    input

/-- Compact-geometric root aggregate: input generator hom target rectangle count is a list length. -/
theorem TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceAnalyticMotive.localizationInput_generatorHom_targetImportedRectangleCount_eq_length
    input

end AnalyticMotives
end LFunctions
end Boundary
