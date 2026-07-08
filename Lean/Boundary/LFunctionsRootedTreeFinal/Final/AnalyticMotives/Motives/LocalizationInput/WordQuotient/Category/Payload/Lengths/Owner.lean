import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Payload.Lengths.Owner

/-!
# Localized word-category payload length facts

This file owns imported-rectangle length invariants for the localized
word-category object and hom constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A wrapped trace object has count equal to rectangle-list length. -/
theorem TraceLocalizedWordObject.ofTraceObject_importedRectangleCount_eq_length
    (object : TraceCorQObject) :
    (TraceLocalizedWordObject.ofTraceObject object).importedRectangleCount =
      (TraceLocalizedWordObject.ofTraceObject object).importedRectangles.length :=
  TraceLocalizedWordObject.importedRectangleCount_eq_length
    (TraceLocalizedWordObject.ofTraceObject object)

/-- The identity hom endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizedWordHom.id_endpointImportedRectangleCount_eq_length
    (object : TraceLocalizedWordObject) :
    (TraceLocalizationWordClass.identity object.underlying).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.identity object.underlying).endpointImportedRectangles.length :=
  TraceLocalizationWordClass.identity_endpointImportedRectangleCount_eq_length
    object.underlying

/-- A composed localized-word hom endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizedWordHom.comp_endpointImportedRectangleCount_eq_length
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp left right).endpointImportedRectangles.length :=
  TraceLocalizationWordClass.comp_endpointImportedRectangleCount_eq_length
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
