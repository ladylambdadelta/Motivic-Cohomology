import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.TraceCalculus.Owner

/-!
# Motive-root unstable payload summaries

This file exposes root summary theorems comparing unstable forward and inverse
payloads with their compact-generator hom endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: input generator hom source rectangles are input source rectangles. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_sourceImportedRectangles
    input

/-- Motive-root summary: input generator hom target rectangles are input target rectangles. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_targetImportedRectangles
    input

/-- Motive-root summary: input generator hom source rectangle count is a list length. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_sourceImportedRectangleCount_eq_length
    input

/-- Motive-root summary: input generator hom target rectangle count is a list length. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_targetImportedRectangleCount_eq_length
    input

/-- Motive-root summary: unstable forward source rectangles match the generator hom source. -/
theorem TraceAnalyticMotive.rootSummary_unstableForward_sourceImportedRectangles_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangles =
      input.generatorHom.sourceImportedRectangles :=
  TraceAnalyticMotive.unstableForward_sourceImportedRectangles_eq_generatorHom
    input

/-- Motive-root summary: unstable forward target rectangles match the generator hom target. -/
theorem TraceAnalyticMotive.rootSummary_unstableForward_targetImportedRectangles_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangles =
      input.generatorHom.targetImportedRectangles :=
  TraceAnalyticMotive.unstableForward_targetImportedRectangles_eq_generatorHom
    input

/-- Motive-root summary: unstable inverse source rectangles match the generator hom target. -/
theorem TraceAnalyticMotive.rootSummary_unstableInverse_sourceImportedRectangles_eq_generatorHom_target
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangles =
      input.generatorHom.targetImportedRectangles :=
  TraceAnalyticMotive.unstableInverse_sourceImportedRectangles_eq_generatorHom_target
    input

/-- Motive-root summary: unstable inverse target rectangles match the generator hom source. -/
theorem TraceAnalyticMotive.rootSummary_unstableInverse_targetImportedRectangles_eq_generatorHom_source
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangles =
      input.generatorHom.sourceImportedRectangles :=
  TraceAnalyticMotive.unstableInverse_targetImportedRectangles_eq_generatorHom_source
    input

/-- Motive-root summary: unstable forward source count matches the generator hom source count. -/
theorem TraceAnalyticMotive.rootSummary_unstableForward_sourceImportedRectangleCount_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangleCount :=
  TraceAnalyticMotive.unstableForward_sourceImportedRectangleCount_eq_generatorHom
    input

/-- Motive-root summary: unstable forward target count matches the generator hom target count. -/
theorem TraceAnalyticMotive.rootSummary_unstableForward_targetImportedRectangleCount_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangleCount :=
  TraceAnalyticMotive.unstableForward_targetImportedRectangleCount_eq_generatorHom
    input

/-- Motive-root summary: unstable inverse source count matches the generator hom target count. -/
theorem TraceAnalyticMotive.rootSummary_unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.generatorHom.targetImportedRectangleCount :=
  TraceAnalyticMotive.unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target
    input

/-- Motive-root summary: unstable inverse target count matches the generator hom source count. -/
theorem TraceAnalyticMotive.rootSummary_unstableInverse_targetImportedRectangleCount_eq_generatorHom_source
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.generatorHom.sourceImportedRectangleCount :=
  TraceAnalyticMotive.unstableInverse_targetImportedRectangleCount_eq_generatorHom_source
    input

/-- Motive-root summary: unstable forward source count is the generator hom source list length. -/
theorem TraceAnalyticMotive.rootSummary_unstableForward_sourceImportedRectangleCount_eq_generatorHom_length
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableForward_sourceImportedRectangleCount_eq_generatorHom_length
    input

/-- Motive-root summary: unstable forward target count is the generator hom target list length. -/
theorem TraceAnalyticMotive.rootSummary_unstableForward_targetImportedRectangleCount_eq_generatorHom_length
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableForward_targetImportedRectangleCount_eq_generatorHom_length
    input

/-- Motive-root summary: unstable inverse source count is the generator hom target list length. -/
theorem TraceAnalyticMotive.rootSummary_unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target_length
    input

/-- Motive-root summary: unstable inverse target count is the generator hom source list length. -/
theorem TraceAnalyticMotive.rootSummary_unstableInverse_targetImportedRectangleCount_eq_generatorHom_source_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableInverse_targetImportedRectangleCount_eq_generatorHom_source_length
    input

end AnalyticMotives
end LFunctions
end Boundary
