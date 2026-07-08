import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Payload.TraceCalculus.Owner

/-!
# Composed word-class payload length facts

This file owns imported-rectangle length invariants for endpoint payload under
composition of formal localized word classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The endpoint imported count of a composed class is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWordClass.comp_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp left right).endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordClass.comp left right)

end AnalyticMotives
end LFunctions
end Boundary
