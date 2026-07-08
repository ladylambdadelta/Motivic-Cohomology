import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Owner

/-!
# Imported finite-rectangle payload for localized input arrows

This file exposes the concrete imported finite-rectangle payload carried by
the forward and inverse arrows attached to a localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forward arrow source endpoint rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.sourceImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceLocalizationWordClass.ofInputForward_sourceImportedRectangles input

/-- The forward arrow target endpoint rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.targetImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceLocalizationWordClass.ofInputForward_targetImportedRectangles input

/-- The inverse arrow source endpoint rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.sourceImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceLocalizationWordClass.ofInputInverse_sourceImportedRectangles input

/-- The inverse arrow target endpoint rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.targetImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceLocalizationWordClass.ofInputInverse_targetImportedRectangles input

/-- The forward arrow source endpoint rectangle count is the input source count. -/
theorem TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.sourceImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  TraceLocalizationWordClass.ofInputForward_sourceImportedRectangleCount input

/-- The forward arrow target endpoint rectangle count is the input target count. -/
theorem TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.targetImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  TraceLocalizationWordClass.ofInputForward_targetImportedRectangleCount input

/-- The inverse arrow source endpoint rectangle count is the input target count. -/
theorem TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.sourceImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  TraceLocalizationWordClass.ofInputInverse_sourceImportedRectangleCount input

/-- The inverse arrow target endpoint rectangle count is the input source count. -/
theorem TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.targetImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  TraceLocalizationWordClass.ofInputInverse_targetImportedRectangleCount input

/-- The forward arrow endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.endpointImportedRectangles =
      input.sourceObject.importedRectangles ++
        input.targetObject.importedRectangles :=
  rfl

/-- The inverse arrow endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.endpointImportedRectangles =
      input.targetObject.importedRectangles ++
        input.sourceObject.importedRectangles :=
  rfl

/-- The forward arrow endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.endpointImportedRectangleCount =
      input.sourceObject.importedRectangleCount +
        input.targetObject.importedRectangleCount :=
  rfl

/-- The inverse arrow endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.endpointImportedRectangleCount =
      input.targetObject.importedRectangleCount +
        input.sourceObject.importedRectangleCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
