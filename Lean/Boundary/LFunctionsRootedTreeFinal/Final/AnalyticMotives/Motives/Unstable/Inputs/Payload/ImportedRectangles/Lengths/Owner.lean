import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.Lengths.Owner

/-!
# Imported-rectangle length facts for unstable localization-input arrows

This file exposes source, target, and endpoint count-as-length facts for
localization-input forward and inverse arrows after they are viewed in the
unstable analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable forward source count is the length of its source rectangle list. -/
theorem TraceLocalizationInput.unstableForward_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.unstableForward.sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_length
    input

/-- The unstable forward target count is the length of its target rectangle list. -/
theorem TraceLocalizationInput.unstableForward_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.unstableForward.targetImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_length
    input

/-- The unstable inverse source count is the length of its source rectangle list. -/
theorem TraceLocalizationInput.unstableInverse_sourceImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.unstableInverse.sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_length
    input

/-- The unstable inverse target count is the length of its target rectangle list. -/
theorem TraceLocalizationInput.unstableInverse_targetImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.unstableInverse.targetImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_length
    input

end AnalyticMotives
end LFunctions
end Boundary
