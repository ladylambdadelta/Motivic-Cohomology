import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.ImportedRectangles.Owner

/-!
# Imported-rectangle counts for unstable localization-input isomorphisms

This file exposes imported-rectangle endpoint lists and counts for the hom and
inverse of each localization-input isomorphism after passage to the unstable
analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable isomorphism hom source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.unstableIso_hom_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.sourceImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_hom_sourceImportedRectangles
    input

/-- The unstable isomorphism hom target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.unstableIso_hom_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.targetImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_hom_targetImportedRectangles
    input

/-- The unstable isomorphism inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.unstableIso_inv_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.sourceImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_inv_sourceImportedRectangles
    input

/-- The unstable isomorphism inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.unstableIso_inv_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.targetImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_inv_targetImportedRectangles
    input

/-- The unstable isomorphism hom source count is the input source count. -/
theorem TraceLocalizationInput.unstableIso_hom_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.sourceImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_hom_sourceImportedRectangleCount
    input

/-- The unstable isomorphism hom target count is the input target count. -/
theorem TraceLocalizationInput.unstableIso_hom_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.targetImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_hom_targetImportedRectangleCount
    input

/-- The unstable isomorphism inverse source count is the input target count. -/
theorem TraceLocalizationInput.unstableIso_inv_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.sourceImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_inv_sourceImportedRectangleCount
    input

/-- The unstable isomorphism inverse target count is the input source count. -/
theorem TraceLocalizationInput.unstableIso_inv_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.targetImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_inv_targetImportedRectangleCount
    input

/-- The unstable isomorphism hom endpoint rectangles are source then target. -/
theorem TraceLocalizationInput.unstableIso_hom_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.endpointImportedRectangles =
      input.sourceObject.importedRectangles ++
        input.targetObject.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_hom_endpointImportedRectangles
    input

/-- The unstable isomorphism inverse endpoint rectangles are target then source. -/
theorem TraceLocalizationInput.unstableIso_inv_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.endpointImportedRectangles =
      input.targetObject.importedRectangles ++
        input.sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_inv_endpointImportedRectangles
    input

/-- The unstable isomorphism hom endpoint count is source plus target. -/
theorem TraceLocalizationInput.unstableIso_hom_endpointImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.endpointImportedRectangleCount =
      input.sourceObject.importedRectangleCount +
        input.targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointImportedRectangleCount
    input

/-- The unstable isomorphism inverse endpoint count is target plus source. -/
theorem TraceLocalizationInput.unstableIso_inv_endpointImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.endpointImportedRectangleCount =
      input.targetObject.importedRectangleCount +
        input.sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointImportedRectangleCount
    input

end AnalyticMotives
end LFunctions
end Boundary
