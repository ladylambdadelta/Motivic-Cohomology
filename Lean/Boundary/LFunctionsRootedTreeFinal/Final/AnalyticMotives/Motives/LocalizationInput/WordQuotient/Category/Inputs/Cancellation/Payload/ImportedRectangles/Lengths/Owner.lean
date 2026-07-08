import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Owner

/-!
# Imported-rectangle length facts for input-cancellation composites

This file records that endpoint imported-rectangle counts on the two
cancellation composites attached to a localization input are the lengths of the
corresponding endpoint rectangle lists.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Hom-inverse cancellation source rectangle count is the length of its source rectangles. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.sourceImportedRectangleCount =
      input.localizedIsoHomInv.sourceImportedRectangles.length :=
  TraceLocalizationWordClass.sourceImportedRectangleCount_eq_length
    input.localizedIsoHomInv

/-- Hom-inverse cancellation target rectangle count is the length of its target rectangles. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.targetImportedRectangleCount =
      input.localizedIsoHomInv.targetImportedRectangles.length :=
  TraceLocalizationWordClass.targetImportedRectangleCount_eq_length
    input.localizedIsoHomInv

/-- Inverse-hom cancellation source rectangle count is the length of its source rectangles. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.sourceImportedRectangleCount =
      input.localizedIsoInvHom.sourceImportedRectangles.length :=
  TraceLocalizationWordClass.sourceImportedRectangleCount_eq_length
    input.localizedIsoInvHom

/-- Inverse-hom cancellation target rectangle count is the length of its target rectangles. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.targetImportedRectangleCount =
      input.localizedIsoInvHom.targetImportedRectangles.length :=
  TraceLocalizationWordClass.targetImportedRectangleCount_eq_length
    input.localizedIsoInvHom

/-- Hom-inverse cancellation endpoint rectangle count is the length of its endpoint rectangles. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.endpointImportedRectangleCount =
      input.localizedIsoHomInv.endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    input.localizedIsoHomInv

/-- Inverse-hom cancellation endpoint rectangle count is the length of its endpoint rectangles. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.endpointImportedRectangleCount =
      input.localizedIsoInvHom.endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    input.localizedIsoInvHom

end AnalyticMotives
end LFunctions
end Boundary
