import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.Lengths.Owner

/-!
# Unstable localization-input payload

This file exposes imported finite-rectangle payload facts for the concrete
localization-input arrows after they are viewed as morphisms in the unstable
analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable forward morphism source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.unstableForward_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
    input

/-- The unstable forward morphism target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.unstableForward_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
    input

/-- The unstable inverse morphism source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.unstableInverse_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangles =
      input.targetObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles
    input

/-- The unstable inverse morphism target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.unstableInverse_targetImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangles =
      input.sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles
    input

/-- The unstable forward morphism source count is the input source count. -/
theorem TraceLocalizationInput.unstableForward_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
    input

/-- The unstable forward morphism target count is the input target count. -/
theorem TraceLocalizationInput.unstableForward_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
    input

/-- The unstable inverse morphism source count is the input target count. -/
theorem TraceLocalizationInput.unstableInverse_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount
    input

/-- The unstable inverse morphism target count is the input source count. -/
theorem TraceLocalizationInput.unstableInverse_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount
    input

/-- The unstable forward morphism endpoint rectangles are source followed by target. -/
theorem TraceLocalizationInput.unstableForward_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointImportedRectangles =
      input.sourceObject.importedRectangles ++
        input.targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles
    input

/-- The unstable inverse morphism endpoint rectangles are target followed by source. -/
theorem TraceLocalizationInput.unstableInverse_endpointImportedRectangles
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointImportedRectangles =
      input.targetObject.importedRectangles ++
        input.sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles
    input

/-- The unstable forward morphism endpoint count is its endpoint list length. -/
theorem TraceLocalizationInput.unstableForward_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointImportedRectangleCount =
      input.unstableForward.endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_length
    input

/-- The unstable inverse morphism endpoint count is its endpoint list length. -/
theorem TraceLocalizationInput.unstableInverse_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointImportedRectangleCount =
      input.unstableInverse.endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_length
    input

end AnalyticMotives
end LFunctions
end Boundary
