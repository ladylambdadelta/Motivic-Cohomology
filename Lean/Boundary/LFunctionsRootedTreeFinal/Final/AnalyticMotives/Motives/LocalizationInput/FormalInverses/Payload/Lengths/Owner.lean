import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.FormalInverses.Payload.Owner

/-!
# Formal localization atom payload length facts

This file owns imported-rectangle length invariants for the oriented endpoint
objects of forward and inverse localization atoms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forward atom source count is the length of its rectangle list. -/
theorem TraceLocalizationAtom.forward_sourceObject_importedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).sourceObject.importedRectangleCount =
      (TraceLocalizationAtom.forward input).sourceObject.importedRectangles.length :=
  TraceLocalizationAtom.sourceObject_importedRectangleCount_eq_length_importedRectangles
    (TraceLocalizationAtom.forward input)

/-- The forward atom target count is the length of its rectangle list. -/
theorem TraceLocalizationAtom.forward_targetObject_importedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).targetObject.importedRectangleCount =
      (TraceLocalizationAtom.forward input).targetObject.importedRectangles.length :=
  TraceLocalizationAtom.targetObject_importedRectangleCount_eq_length_importedRectangles
    (TraceLocalizationAtom.forward input)

/-- The inverse atom source count is the length of its rectangle list. -/
theorem TraceLocalizationAtom.inverse_sourceObject_importedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).sourceObject.importedRectangleCount =
      (TraceLocalizationAtom.inverse input).sourceObject.importedRectangles.length :=
  TraceLocalizationAtom.sourceObject_importedRectangleCount_eq_length_importedRectangles
    (TraceLocalizationAtom.inverse input)

/-- The inverse atom target count is the length of its rectangle list. -/
theorem TraceLocalizationAtom.inverse_targetObject_importedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).targetObject.importedRectangleCount =
      (TraceLocalizationAtom.inverse input).targetObject.importedRectangles.length :=
  TraceLocalizationAtom.targetObject_importedRectangleCount_eq_length_importedRectangles
    (TraceLocalizationAtom.inverse input)

end AnalyticMotives
end LFunctions
end Boundary
