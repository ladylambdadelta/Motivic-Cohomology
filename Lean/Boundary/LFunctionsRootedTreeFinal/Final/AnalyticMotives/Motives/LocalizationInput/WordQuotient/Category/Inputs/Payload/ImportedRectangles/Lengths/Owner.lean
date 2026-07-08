import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Lengths.Owner

/-!
# Imported-rectangle length facts for localized input arrows

This file records that localized input-arrow imported-rectangle endpoint
counts are the lengths of their endpoint rectangle lists.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forward arrow source endpoint count is the length of its source rectangle list. -/
theorem TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.sourceImportedRectangleCount =
      input.localizedForwardArrow.sourceImportedRectangles.length :=
  TraceLocalizationWordClass.sourceImportedRectangleCount_eq_length
    input.localizedForwardArrow

/-- The forward arrow target endpoint count is the length of its target rectangle list. -/
theorem TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.targetImportedRectangleCount =
      input.localizedForwardArrow.targetImportedRectangles.length :=
  TraceLocalizationWordClass.targetImportedRectangleCount_eq_length
    input.localizedForwardArrow

/-- The inverse arrow source endpoint count is the length of its source rectangle list. -/
theorem TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.sourceImportedRectangleCount =
      input.localizedInverseArrow.sourceImportedRectangles.length :=
  TraceLocalizationWordClass.sourceImportedRectangleCount_eq_length
    input.localizedInverseArrow

/-- The inverse arrow target endpoint count is the length of its target rectangle list. -/
theorem TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.targetImportedRectangleCount =
      input.localizedInverseArrow.targetImportedRectangles.length :=
  TraceLocalizationWordClass.targetImportedRectangleCount_eq_length
    input.localizedInverseArrow

/-- The forward arrow endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.endpointImportedRectangleCount =
      input.localizedForwardArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    input.localizedForwardArrow

/-- The inverse arrow endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.endpointImportedRectangleCount =
      input.localizedInverseArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    input.localizedInverseArrow

end AnalyticMotives
end LFunctions
end Boundary
