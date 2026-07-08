import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.Owner

/-!
# Generic inverted-input imported-rectangle payload

This file exposes the imported finite-rectangle endpoint payload carried by
the hom and inverse arrows of the generic localized-word isomorphism attached
to a concrete localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The generic localized-input isomorphism hom source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.localizedWordIso_hom_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.sourceImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
    input

/-- The generic localized-input isomorphism hom target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.localizedWordIso_hom_targetImportedRectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.targetImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
    input

/-- The generic localized-input isomorphism inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.localizedWordIso_inv_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.sourceImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles
    input

/-- The generic localized-input isomorphism inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.localizedWordIso_inv_targetImportedRectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.targetImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles
    input

/-- The generic localized-input isomorphism hom source count is the input source count. -/
theorem TraceLocalizationInput.localizedWordIso_hom_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.sourceImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
    input

/-- The generic localized-input isomorphism hom target count is the input target count. -/
theorem TraceLocalizationInput.localizedWordIso_hom_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.targetImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
    input

/-- The generic localized-input isomorphism inverse source count is the input target count. -/
theorem TraceLocalizationInput.localizedWordIso_inv_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.sourceImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount
    input

/-- The generic localized-input isomorphism inverse target count is the input source count. -/
theorem TraceLocalizationInput.localizedWordIso_inv_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.targetImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount
    input

/-- The generic localized-input isomorphism hom endpoint rectangles are source then target. -/
theorem TraceLocalizationInput.localizedWordIso_hom_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.endpointImportedRectangles =
      input.sourceObject.importedRectangles ++
        input.targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles
    input

/-- The generic localized-input isomorphism inverse endpoint rectangles are target then source. -/
theorem TraceLocalizationInput.localizedWordIso_inv_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.endpointImportedRectangles =
      input.targetObject.importedRectangles ++
        input.sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles
    input

/-- The generic localized-input isomorphism hom endpoint count is source count plus target count. -/
theorem TraceLocalizationInput.localizedWordIso_hom_endpointImportedRectangleCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.endpointImportedRectangleCount =
      input.sourceObject.importedRectangleCount +
        input.targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount
    input

/-- The generic localized-input isomorphism inverse endpoint count is target count plus source count. -/
theorem TraceLocalizationInput.localizedWordIso_inv_endpointImportedRectangleCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.endpointImportedRectangleCount =
      input.targetObject.importedRectangleCount +
        input.sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount
    input

end AnalyticMotives
end LFunctions
end Boundary
