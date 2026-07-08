import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.GeneratorHom.Owner

/-!
# Root generator-hom compatibility for unstable inputs

This file mirrors the compatibility between unstable localization arrows and
compact-generator morphisms under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Root unstable forward source rectangles agree with compact-generator hom source rectangles. -/
theorem TraceAnalyticMotive.unstableForward_sourceImportedRectangles_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangles =
      input.generatorHom.sourceImportedRectangles :=
  TraceLocalizationInput.unstableForward_sourceImportedRectangles_eq_generatorHom
    input

/-- Root unstable forward target rectangles agree with compact-generator hom target rectangles. -/
theorem TraceAnalyticMotive.unstableForward_targetImportedRectangles_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangles =
      input.generatorHom.targetImportedRectangles :=
  TraceLocalizationInput.unstableForward_targetImportedRectangles_eq_generatorHom
    input

/-- Root unstable forward source count agrees with compact-generator hom source count. -/
theorem TraceAnalyticMotive.unstableForward_sourceImportedRectangleCount_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangleCount :=
  TraceLocalizationInput.unstableForward_sourceImportedRectangleCount_eq_generatorHom
    input

/-- Root unstable forward target count agrees with compact-generator hom target count. -/
theorem TraceAnalyticMotive.unstableForward_targetImportedRectangleCount_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangleCount :=
  TraceLocalizationInput.unstableForward_targetImportedRectangleCount_eq_generatorHom
    input

/-- Root unstable forward source count is the compact-generator source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableForward_sourceImportedRectangleCount_eq_generatorHom_length
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceLocalizationInput.unstableForward_sourceImportedRectangleCount_eq_generatorHom_length
    input

/-- Root unstable forward target count is the compact-generator target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableForward_targetImportedRectangleCount_eq_generatorHom_length
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceLocalizationInput.unstableForward_targetImportedRectangleCount_eq_generatorHom_length
    input

/-- Root unstable inverse source rectangles agree with compact-generator hom target rectangles. -/
theorem TraceAnalyticMotive.unstableInverse_sourceImportedRectangles_eq_generatorHom_target
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangles =
      input.generatorHom.targetImportedRectangles :=
  TraceLocalizationInput.unstableInverse_sourceImportedRectangles_eq_generatorHom_target
    input

/-- Root unstable inverse target rectangles agree with compact-generator hom source rectangles. -/
theorem TraceAnalyticMotive.unstableInverse_targetImportedRectangles_eq_generatorHom_source
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangles =
      input.generatorHom.sourceImportedRectangles :=
  TraceLocalizationInput.unstableInverse_targetImportedRectangles_eq_generatorHom_source
    input

/-- Root unstable inverse source count agrees with compact-generator hom target count. -/
theorem TraceAnalyticMotive.unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.generatorHom.targetImportedRectangleCount :=
  TraceLocalizationInput.unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target
    input

/-- Root unstable inverse target count agrees with compact-generator hom source count. -/
theorem TraceAnalyticMotive.unstableInverse_targetImportedRectangleCount_eq_generatorHom_source
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.generatorHom.sourceImportedRectangleCount :=
  TraceLocalizationInput.unstableInverse_targetImportedRectangleCount_eq_generatorHom_source
    input

/-- Root unstable inverse source count is the compact-generator target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  TraceLocalizationInput.unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target_length
    input

/-- Root unstable inverse target count is the compact-generator source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableInverse_targetImportedRectangleCount_eq_generatorHom_source_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  TraceLocalizationInput.unstableInverse_targetImportedRectangleCount_eq_generatorHom_source_length
    input

end AnalyticMotives
end LFunctions
end Boundary
