import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.Lengths.Owner

/-!
# Generic inverted-input payload length facts

This file owns imported-rectangle endpoint length facts for the hom and
inverse arrows of the generic localized-word isomorphism attached to a concrete
localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The generic localized-input isomorphism hom endpoint count is its endpoint list length. -/
theorem TraceLocalizationInput.localizedWordIso_hom_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_length
    input

/-- The generic localized-input isomorphism inverse endpoint count is its endpoint list length. -/
theorem TraceLocalizationInput.localizedWordIso_inv_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_length
    input

/-- The generic localized-input isomorphism hom source count is its source list length. -/
theorem TraceLocalizationInput.localizedWordIso_hom_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_length
    input

/-- The generic localized-input isomorphism hom target count is its target list length. -/
theorem TraceLocalizationInput.localizedWordIso_hom_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_length
    input

/-- The generic localized-input isomorphism inverse source count is its source list length. -/
theorem TraceLocalizationInput.localizedWordIso_inv_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_length
    input

/-- The generic localized-input isomorphism inverse target count is its target list length. -/
theorem TraceLocalizationInput.localizedWordIso_inv_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_length
    input

end AnalyticMotives
end LFunctions
end Boundary
