import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.Owner

/-!
# Localization word-class payload length facts

This file owns imported-rectangle length invariants for the endpoint payload of
formal localized word-class constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A represented word class endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWordClass.ofWord_endpointImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.ofWord word).endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordClass.ofWord word)

/-- The identity word class endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWordClass.identity_endpointImportedRectangleCount_eq_length
    (object : TraceCorQObject) :
    (TraceLocalizationWordClass.identity object).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.identity object).endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordClass.identity object)

/-- A forward-input word class endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWordClass.ofInputForward_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.ofInputForward input).endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordClass.ofInputForward input)

/-- An inverse-input word class endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWordClass.ofInputInverse_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.ofInputInverse input).endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordClass.ofInputInverse input)

end AnalyticMotives
end LFunctions
end Boundary
