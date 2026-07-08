import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.UnstablePayload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.Unstable.Owner

/-!
# Top-root unstable payload summaries

This file exposes comparisons between unstable forward and inverse payloads
and their compact-generator hom endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public motive summary: input generator hom source rectangles are input source rectangles. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_sourceImportedRectangles
    input

/-- Public motive summary: input generator hom target rectangles are input target rectangles. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_targetImportedRectangles
    input

/-- Public motive summary: input generator hom source rectangle count is a list length. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.generatorHom.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_sourceImportedRectangleCount_eq_length
    input

/-- Public motive summary: input generator hom target rectangle count is a list length. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.generatorHom.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_targetImportedRectangleCount_eq_length
    input

/-- Public motive summary: unstable forward source rectangles match the generator hom source. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForward_sourceImportedRectangles_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangles =
      input.generatorHom.sourceImportedRectangles :=
  TraceAnalyticMotive.rootSummary_unstableForward_sourceImportedRectangles_eq_generatorHom
    input

/-- Public motive summary: unstable forward target rectangles match the generator hom target. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForward_targetImportedRectangles_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangles =
      input.generatorHom.targetImportedRectangles :=
  TraceAnalyticMotive.rootSummary_unstableForward_targetImportedRectangles_eq_generatorHom
    input

/-- Public motive summary: unstable inverse source rectangles match the generator hom target. -/
theorem AnalyticMotivesRoot.rootSummary_unstableInverse_sourceImportedRectangles_eq_generatorHom_target
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangles =
      input.generatorHom.targetImportedRectangles :=
  TraceAnalyticMotive.rootSummary_unstableInverse_sourceImportedRectangles_eq_generatorHom_target
    input

/-- Public motive summary: unstable inverse target rectangles match the generator hom source. -/
theorem AnalyticMotivesRoot.rootSummary_unstableInverse_targetImportedRectangles_eq_generatorHom_source
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangles =
      input.generatorHom.sourceImportedRectangles :=
  TraceAnalyticMotive.rootSummary_unstableInverse_targetImportedRectangles_eq_generatorHom_source
    input

/-- Public motive summary: unstable forward source count matches the generator hom source count. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForward_sourceImportedRectangleCount_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangleCount :=
  TraceAnalyticMotive.rootSummary_unstableForward_sourceImportedRectangleCount_eq_generatorHom
    input

/-- Public motive summary: unstable forward target count matches the generator hom target count. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForward_targetImportedRectangleCount_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangleCount :=
  TraceAnalyticMotive.rootSummary_unstableForward_targetImportedRectangleCount_eq_generatorHom
    input

/-- Public motive summary: unstable inverse source count matches the generator hom target count. -/
theorem AnalyticMotivesRoot.rootSummary_unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.generatorHom.targetImportedRectangleCount :=
  TraceAnalyticMotive.rootSummary_unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target
    input

/-- Public motive summary: unstable inverse target count matches the generator hom source count. -/
theorem AnalyticMotivesRoot.rootSummary_unstableInverse_targetImportedRectangleCount_eq_generatorHom_source
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.generatorHom.sourceImportedRectangleCount :=
  TraceAnalyticMotive.rootSummary_unstableInverse_targetImportedRectangleCount_eq_generatorHom_source
    input

/-- Public motive summary: unstable forward source count is the generator hom source list length. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForward_sourceImportedRectangleCount_eq_generatorHom_length
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.rootSummary_unstableForward_sourceImportedRectangleCount_eq_generatorHom_length
    input

/-- Public motive summary: unstable forward target count is the generator hom target list length. -/
theorem AnalyticMotivesRoot.rootSummary_unstableForward_targetImportedRectangleCount_eq_generatorHom_length
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceAnalyticMotive.rootSummary_unstableForward_targetImportedRectangleCount_eq_generatorHom_length
    input

/-- Public motive summary: unstable inverse source count is the generator hom target list length. -/
theorem AnalyticMotivesRoot.rootSummary_unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceAnalyticMotive.rootSummary_unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target_length
    input

/-- Public motive summary: unstable inverse target count is the generator hom source list length. -/
theorem AnalyticMotivesRoot.rootSummary_unstableInverse_targetImportedRectangleCount_eq_generatorHom_source_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.rootSummary_unstableInverse_targetImportedRectangleCount_eq_generatorHom_source_length
    input

end AnalyticMotives
end LFunctions
end Boundary
