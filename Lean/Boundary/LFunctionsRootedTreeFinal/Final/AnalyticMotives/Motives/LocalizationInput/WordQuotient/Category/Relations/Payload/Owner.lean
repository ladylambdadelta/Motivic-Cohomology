import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Relations.Payload.Lengths.Owner

/-!
# Payload for localized word relations

This file owns the payload surface for generated localized word relations.  The
nested length owner proves endpoint imported-rectangle count invariants for the
left and right relation arrows; this owner re-exposes those facts at the
relation payload boundary.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The relation payload surface exposes left-arrow endpoint rectangle counts. -/
theorem TraceLocalizationWordRelationPayload.left_localizedArrow_endpointImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left right : TraceLocalizationWord source target}
    (relation : TraceLocalizationWordRelation left right) :
    left.localizedArrow.endpointImportedRectangleCount =
      left.localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.left_localizedArrow_endpointImportedRectangleCount_eq_length
    relation

/-- The relation payload surface exposes right-arrow endpoint rectangle counts. -/
theorem TraceLocalizationWordRelationPayload.right_localizedArrow_endpointImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left right : TraceLocalizationWord source target}
    (relation : TraceLocalizationWordRelation left right) :
    right.localizedArrow.endpointImportedRectangleCount =
      right.localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.right_localizedArrow_endpointImportedRectangleCount_eq_length
    relation

/-- The relation payload surface exposes forward-inverse left endpoint counts. -/
theorem TraceLocalizationWordRelationPayload.forwardInverse_left_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.forwardThenInverse input).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.forwardThenInverse input).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.forwardInverse_left_endpointImportedRectangleCount_eq_length
    input

/-- The relation payload surface exposes forward-inverse right endpoint counts. -/
theorem TraceLocalizationWordRelationPayload.forwardInverse_right_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.identity input.sourceObject).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.identity input.sourceObject).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.forwardInverse_right_endpointImportedRectangleCount_eq_length
    input

/-- The relation payload surface exposes inverse-forward left endpoint counts. -/
theorem TraceLocalizationWordRelationPayload.inverseForward_left_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.inverseThenForward input).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.inverseThenForward input).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.inverseForward_left_endpointImportedRectangleCount_eq_length
    input

/-- The relation payload surface exposes inverse-forward right endpoint counts. -/
theorem TraceLocalizationWordRelationPayload.inverseForward_right_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.identity input.targetObject).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.identity input.targetObject).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.inverseForward_right_endpointImportedRectangleCount_eq_length
    input

/-- The relation payload surface exposes prefix-closure left endpoint counts. -/
theorem TraceLocalizationWordRelationPayload.withPrefix_left_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord second third}
    (prefixWord : TraceLocalizationWord first second)
    (relation : TraceLocalizationWordRelation left right) :
    (TraceLocalizationWord.comp prefixWord left).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.comp prefixWord left).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.withPrefix_left_endpointImportedRectangleCount_eq_length
    prefixWord
    relation

/-- The relation payload surface exposes prefix-closure right endpoint counts. -/
theorem TraceLocalizationWordRelationPayload.withPrefix_right_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord second third}
    (prefixWord : TraceLocalizationWord first second)
    (relation : TraceLocalizationWordRelation left right) :
    (TraceLocalizationWord.comp prefixWord right).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.comp prefixWord right).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.withPrefix_right_endpointImportedRectangleCount_eq_length
    prefixWord
    relation

/-- The relation payload surface exposes suffix-closure left endpoint counts. -/
theorem TraceLocalizationWordRelationPayload.withSuffix_left_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord first second}
    (relation : TraceLocalizationWordRelation left right)
    (suffix : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left suffix).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.comp left suffix).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.withSuffix_left_endpointImportedRectangleCount_eq_length
    relation
    suffix

/-- The relation payload surface exposes suffix-closure right endpoint counts. -/
theorem TraceLocalizationWordRelationPayload.withSuffix_right_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord first second}
    (relation : TraceLocalizationWordRelation left right)
    (suffix : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp right suffix).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.comp right suffix).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordRelation.withSuffix_right_endpointImportedRectangleCount_eq_length
    relation
    suffix

end AnalyticMotives
end LFunctions
end Boundary
