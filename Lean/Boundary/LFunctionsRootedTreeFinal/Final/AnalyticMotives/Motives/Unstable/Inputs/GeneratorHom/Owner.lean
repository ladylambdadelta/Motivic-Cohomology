import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Payload.Owner

/-!
# Generator-hom compatibility for unstable localization inputs

This file compares the endpoint payload of the unstable localization arrows
with the compact-generator morphism attached to the same localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable forward source rectangles agree with the compact-generator hom source rectangles. -/
theorem TraceLocalizationInput.unstableForward_sourceImportedRectangles_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangles =
      input.generatorHom.sourceImportedRectangles :=
  Eq.trans
    (TraceLocalizationInput.unstableForward_sourceImportedRectangles input)
    (Eq.symm
      (TraceLocalizationInput.generatorHom_sourceImportedRectangles input))

/-- The unstable forward target rectangles agree with the compact-generator hom target rectangles. -/
theorem TraceLocalizationInput.unstableForward_targetImportedRectangles_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangles =
      input.generatorHom.targetImportedRectangles :=
  Eq.trans
    (TraceLocalizationInput.unstableForward_targetImportedRectangles input)
    (Eq.symm
      (TraceLocalizationInput.generatorHom_targetImportedRectangles input))

/-- The unstable forward source count agrees with the compact-generator hom source count. -/
theorem TraceLocalizationInput.unstableForward_sourceImportedRectangleCount_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangleCount :=
  Eq.trans
    (TraceLocalizationInput.unstableForward_sourceImportedRectangleCount input)
    (Eq.symm
      (TraceLocalizationInput.generatorHom_sourceImportedRectangleCount input))

/-- The unstable forward target count agrees with the compact-generator hom target count. -/
theorem TraceLocalizationInput.unstableForward_targetImportedRectangleCount_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangleCount :=
  Eq.trans
    (TraceLocalizationInput.unstableForward_targetImportedRectangleCount input)
    (Eq.symm
      (TraceLocalizationInput.generatorHom_targetImportedRectangleCount input))

/-- The unstable forward source count is the compact-generator source rectangle-list length. -/
theorem TraceLocalizationInput.unstableForward_sourceImportedRectangleCount_eq_generatorHom_length
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  Eq.trans
    (TraceLocalizationInput.unstableForward_sourceImportedRectangleCount_eq_generatorHom input)
    (TraceLocalizationInput.generatorHom_sourceImportedRectangleCount_eq_length input)

/-- The unstable forward target count is the compact-generator target rectangle-list length. -/
theorem TraceLocalizationInput.unstableForward_targetImportedRectangleCount_eq_generatorHom_length
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  Eq.trans
    (TraceLocalizationInput.unstableForward_targetImportedRectangleCount_eq_generatorHom input)
    (TraceLocalizationInput.generatorHom_targetImportedRectangleCount_eq_length input)

/-- The unstable inverse source rectangles agree with the compact-generator hom target rectangles. -/
theorem TraceLocalizationInput.unstableInverse_sourceImportedRectangles_eq_generatorHom_target
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangles =
      input.generatorHom.targetImportedRectangles :=
  Eq.trans
    (TraceLocalizationInput.unstableInverse_sourceImportedRectangles input)
    (Eq.symm
      (TraceLocalizationInput.generatorHom_targetImportedRectangles input))

/-- The unstable inverse target rectangles agree with the compact-generator hom source rectangles. -/
theorem TraceLocalizationInput.unstableInverse_targetImportedRectangles_eq_generatorHom_source
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangles =
      input.generatorHom.sourceImportedRectangles :=
  Eq.trans
    (TraceLocalizationInput.unstableInverse_targetImportedRectangles input)
    (Eq.symm
      (TraceLocalizationInput.generatorHom_sourceImportedRectangles input))

/-- The unstable inverse source count agrees with the compact-generator hom target count. -/
theorem TraceLocalizationInput.unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.generatorHom.targetImportedRectangleCount :=
  Eq.trans
    (TraceLocalizationInput.unstableInverse_sourceImportedRectangleCount input)
    (Eq.symm
      (TraceLocalizationInput.generatorHom_targetImportedRectangleCount input))

/-- The unstable inverse target count agrees with the compact-generator hom source count. -/
theorem TraceLocalizationInput.unstableInverse_targetImportedRectangleCount_eq_generatorHom_source
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.generatorHom.sourceImportedRectangleCount :=
  Eq.trans
    (TraceLocalizationInput.unstableInverse_targetImportedRectangleCount input)
    (Eq.symm
      (TraceLocalizationInput.generatorHom_sourceImportedRectangleCount input))

/-- The unstable inverse source count is the compact-generator target rectangle-list length. -/
theorem TraceLocalizationInput.unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.generatorHom.targetImportedRectangles.length :=
  Eq.trans
    (TraceLocalizationInput.unstableInverse_sourceImportedRectangleCount_eq_generatorHom_target input)
    (TraceLocalizationInput.generatorHom_targetImportedRectangleCount_eq_length input)

/-- The unstable inverse target count is the compact-generator source rectangle-list length. -/
theorem TraceLocalizationInput.unstableInverse_targetImportedRectangleCount_eq_generatorHom_source_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.generatorHom.sourceImportedRectangles.length :=
  Eq.trans
    (TraceLocalizationInput.unstableInverse_targetImportedRectangleCount_eq_generatorHom_source input)
    (TraceLocalizationInput.generatorHom_sourceImportedRectangleCount_eq_length input)

end AnalyticMotives
end LFunctions
end Boundary
