import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Relations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Words.Payload.Owner

/-!
# Relation-side localized arrow payload length facts

This file owns imported-rectangle length invariants for localized arrows
appearing as the left and right sides of generated word relations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left side of a generated localized arrow relation has endpoint count equal to length. -/
theorem TraceLocalizationWordRelation.left_localizedArrow_endpointImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left right : TraceLocalizationWord source target}
    (_relation : TraceLocalizationWordRelation left right) :
    left.localizedArrow.endpointImportedRectangleCount =
      left.localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_endpointImportedRectangleCount_eq_length
    left

/-- The right side of a generated localized arrow relation has endpoint count equal to length. -/
theorem TraceLocalizationWordRelation.right_localizedArrow_endpointImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left right : TraceLocalizationWord source target}
    (_relation : TraceLocalizationWordRelation left right) :
    right.localizedArrow.endpointImportedRectangleCount =
      right.localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_endpointImportedRectangleCount_eq_length
    right

/-- The forward-inverse cancellation left arrow has endpoint count equal to length. -/
theorem TraceLocalizationWordRelation.forwardInverse_left_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.forwardThenInverse input).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.forwardThenInverse input).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.left_localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordRelation.forwardInverse input)

/-- The forward-inverse cancellation right arrow has endpoint count equal to length. -/
theorem TraceLocalizationWordRelation.forwardInverse_right_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.identity input.sourceObject).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.identity input.sourceObject).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.right_localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordRelation.forwardInverse input)

/-- The inverse-forward cancellation left arrow has endpoint count equal to length. -/
theorem TraceLocalizationWordRelation.inverseForward_left_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.inverseThenForward input).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.inverseThenForward input).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.left_localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordRelation.inverseForward input)

/-- The inverse-forward cancellation right arrow has endpoint count equal to length. -/
theorem TraceLocalizationWordRelation.inverseForward_right_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.identity input.targetObject).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.identity input.targetObject).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.right_localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordRelation.inverseForward input)

/-- Prefix closure left arrow has endpoint count equal to length. -/
theorem TraceLocalizationWordRelation.withPrefix_left_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord second third}
    (prefixWord : TraceLocalizationWord first second)
    (relation : TraceLocalizationWordRelation left right) :
    (TraceLocalizationWord.comp prefixWord left).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.comp prefixWord left).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.left_localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordRelation.withPrefix prefixWord relation)

/-- Prefix closure right arrow has endpoint count equal to length. -/
theorem TraceLocalizationWordRelation.withPrefix_right_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord second third}
    (prefixWord : TraceLocalizationWord first second)
    (relation : TraceLocalizationWordRelation left right) :
    (TraceLocalizationWord.comp prefixWord right).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.comp prefixWord right).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.right_localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordRelation.withPrefix prefixWord relation)

/-- Suffix closure left arrow has endpoint count equal to length. -/
theorem TraceLocalizationWordRelation.withSuffix_left_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord first second}
    (relation : TraceLocalizationWordRelation left right)
    (suffix : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left suffix).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.comp left suffix).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.left_localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordRelation.withSuffix relation suffix)

/-- Suffix closure right arrow has endpoint count equal to length. -/
theorem TraceLocalizationWordRelation.withSuffix_right_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord first second}
    (relation : TraceLocalizationWordRelation left right)
    (suffix : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp right suffix).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.comp right suffix).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.right_localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWordRelation.withSuffix relation suffix)

end AnalyticMotives
end LFunctions
end Boundary
