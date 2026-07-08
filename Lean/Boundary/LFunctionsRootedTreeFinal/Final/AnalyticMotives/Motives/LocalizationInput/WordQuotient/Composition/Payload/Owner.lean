import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.Owner

/-!
# Endpoint payload for composed localized word classes

This file records how imported finite-rectangle endpoint payload behaves under
composition in the localized word-class category.

The payload is endpoint data: composition keeps the left source endpoint and
the right target endpoint.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composition keeps the left word class source endpoint rectangles. -/
theorem TraceLocalizationWordClass.comp_sourceImportedRectangles
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).sourceImportedRectangles =
      left.sourceImportedRectangles :=
  rfl

/-- Composition keeps the right word class target endpoint rectangles. -/
theorem TraceLocalizationWordClass.comp_targetImportedRectangles
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).targetImportedRectangles =
      right.targetImportedRectangles :=
  rfl

/-- Composition keeps the left word class source endpoint count. -/
theorem TraceLocalizationWordClass.comp_sourceImportedRectangleCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).sourceImportedRectangleCount =
      left.sourceImportedRectangleCount :=
  rfl

/-- Composition keeps the right word class target endpoint count. -/
theorem TraceLocalizationWordClass.comp_targetImportedRectangleCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).targetImportedRectangleCount =
      right.targetImportedRectangleCount :=
  rfl

/-- The endpoint rectangles of a composite are the left source rectangles followed by right target rectangles. -/
theorem TraceLocalizationWordClass.comp_endpointImportedRectangles
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangles =
      left.sourceImportedRectangles ++
        right.targetImportedRectangles :=
  rfl

/-- The endpoint imported count of a composite is the left source count plus right target count. -/
theorem TraceLocalizationWordClass.comp_endpointImportedRectangleCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangleCount =
      left.sourceImportedRectangleCount +
        right.targetImportedRectangleCount :=
  rfl

/-- The source endpoint count of a composed class is counted by its source rectangle list. -/
theorem TraceLocalizationWordClass.comp_sourceImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).sourceImportedRectangleCount =
      (TraceLocalizationWordClass.comp left right).sourceImportedRectangles.length :=
  TraceLocalizationWordClass.sourceImportedRectangleCount_eq_length
    (TraceLocalizationWordClass.comp left right)

/-- The target endpoint count of a composed class is counted by its target rectangle list. -/
theorem TraceLocalizationWordClass.comp_targetImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).targetImportedRectangleCount =
      (TraceLocalizationWordClass.comp left right).targetImportedRectangles.length :=
  TraceLocalizationWordClass.targetImportedRectangleCount_eq_length
    (TraceLocalizationWordClass.comp left right)

end AnalyticMotives
end LFunctions
end Boundary
