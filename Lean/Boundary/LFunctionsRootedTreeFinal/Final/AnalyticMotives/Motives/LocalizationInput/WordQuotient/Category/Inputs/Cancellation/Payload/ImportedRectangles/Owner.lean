import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.ImportedRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.ImportedRectangles.LedgerCounts.Owner

/-!
# Imported-rectangle payload for input-cancellation composites

This file records the endpoint finite-rectangle payload carried by the two
cancellation composites attached to a localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The hom-inverse cancellation composite has the input source rectangles as source endpoint. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.sourceImportedRectangles =
      input.localizedSourceObject.importedRectangles :=
  rfl

/-- The hom-inverse cancellation composite has the input source rectangles as target endpoint. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.targetImportedRectangles =
      input.localizedSourceObject.importedRectangles :=
  rfl

/-- The inverse-hom cancellation composite has the input target rectangles as source endpoint. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.sourceImportedRectangles =
      input.localizedTargetObject.importedRectangles :=
  rfl

/-- The inverse-hom cancellation composite has the input target rectangles as target endpoint. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.targetImportedRectangles =
      input.localizedTargetObject.importedRectangles :=
  rfl

/-- Hom-inverse cancellation source rectangle count is the source object's rectangle count. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.sourceImportedRectangleCount =
      input.localizedSourceObject.importedRectangleCount :=
  rfl

/-- Hom-inverse cancellation target rectangle count is the source object's rectangle count. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.targetImportedRectangleCount =
      input.localizedSourceObject.importedRectangleCount :=
  rfl

/-- Inverse-hom cancellation source rectangle count is the target object's rectangle count. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.sourceImportedRectangleCount =
      input.localizedTargetObject.importedRectangleCount :=
  rfl

/-- Inverse-hom cancellation target rectangle count is the target object's rectangle count. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.targetImportedRectangleCount =
      input.localizedTargetObject.importedRectangleCount :=
  rfl

/-- Hom-inverse cancellation endpoint rectangles are source rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.endpointImportedRectangles =
      input.localizedSourceObject.importedRectangles ++
        input.localizedSourceObject.importedRectangles :=
  rfl

/-- Inverse-hom cancellation endpoint rectangles are target rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.endpointImportedRectangles =
      input.localizedTargetObject.importedRectangles ++
        input.localizedTargetObject.importedRectangles :=
  rfl

/-- Hom-inverse cancellation endpoint rectangle count is source count plus source count. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.endpointImportedRectangleCount =
      input.localizedSourceObject.importedRectangleCount +
        input.localizedSourceObject.importedRectangleCount :=
  rfl

/-- Inverse-hom cancellation endpoint rectangle count is target count plus target count. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.endpointImportedRectangleCount =
      input.localizedTargetObject.importedRectangleCount +
        input.localizedTargetObject.importedRectangleCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
