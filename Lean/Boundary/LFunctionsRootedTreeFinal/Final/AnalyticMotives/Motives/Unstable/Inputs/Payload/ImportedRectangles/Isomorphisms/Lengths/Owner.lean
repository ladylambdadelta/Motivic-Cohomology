import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.Lengths.Owner

/-!
# Imported-rectangle length facts for unstable localization-input isomorphisms

This file exposes count-as-length facts for imported-rectangle endpoints of the
hom and inverse of each localization-input isomorphism after passage to the
unstable analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable isomorphism hom endpoint count is its endpoint list length. -/
theorem TraceLocalizationInput.unstableIso_hom_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.endpointImportedRectangleCount =
      input.unstableIso.hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedWordIso_hom_endpointImportedRectangleCount_eq_length
    input

/-- The unstable isomorphism inverse endpoint count is its endpoint list length. -/
theorem TraceLocalizationInput.unstableIso_inv_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.endpointImportedRectangleCount =
      input.unstableIso.inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedWordIso_inv_endpointImportedRectangleCount_eq_length
    input

/-- The unstable isomorphism hom source count is its source list length. -/
theorem TraceLocalizationInput.unstableIso_hom_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.sourceImportedRectangleCount =
      input.unstableIso.hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedWordIso_hom_sourceImportedRectangleCount_eq_length
    input

/-- The unstable isomorphism hom target count is its target list length. -/
theorem TraceLocalizationInput.unstableIso_hom_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.targetImportedRectangleCount =
      input.unstableIso.hom.targetImportedRectangles.length :=
  TraceLocalizationInput.localizedWordIso_hom_targetImportedRectangleCount_eq_length
    input

/-- The unstable isomorphism inverse source count is its source list length. -/
theorem TraceLocalizationInput.unstableIso_inv_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.sourceImportedRectangleCount =
      input.unstableIso.inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedWordIso_inv_sourceImportedRectangleCount_eq_length
    input

/-- The unstable isomorphism inverse target count is its target list length. -/
theorem TraceLocalizationInput.unstableIso_inv_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.targetImportedRectangleCount =
      input.unstableIso.inv.targetImportedRectangles.length :=
  TraceLocalizationInput.localizedWordIso_inv_targetImportedRectangleCount_eq_length
    input

end AnalyticMotives
end LFunctions
end Boundary
