import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Payload.Owner

/-!
# Endpoint payload in the localized word category

This file exposes imported finite-rectangle endpoint payload through the
localized word-category wrapper.

The category wrapper does not add analytic content: object payload is the
payload of the underlying trace object, and hom payload is the endpoint payload
of the localized word class.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Imported rectangles carried by a localized-word object. -/
def TraceLocalizedWordObject.importedRectangles
    (object : TraceLocalizedWordObject) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  object.underlying.importedRectangles

/-- Imported-rectangle count carried by a localized-word object. -/
def TraceLocalizedWordObject.importedRectangleCount
    (object : TraceLocalizedWordObject) :
    Nat :=
  object.underlying.importedRectangleCount

/-- The object imported count is counted by its imported rectangle list. -/
theorem TraceLocalizedWordObject.importedRectangleCount_eq_length
    (object : TraceLocalizedWordObject) :
    object.importedRectangleCount =
      object.importedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    object.underlying

/-- The object constructor preserves imported rectangles. -/
theorem TraceLocalizedWordObject.ofTraceObject_importedRectangles
    (object : TraceCorQObject) :
    (TraceLocalizedWordObject.ofTraceObject object).importedRectangles =
      object.importedRectangles :=
  rfl

/-- The object constructor preserves imported-rectangle count. -/
theorem TraceLocalizedWordObject.ofTraceObject_importedRectangleCount
    (object : TraceCorQObject) :
    (TraceLocalizedWordObject.ofTraceObject object).importedRectangleCount =
      object.importedRectangleCount :=
  rfl

/-- Source endpoint rectangles carried by a localized-word hom. -/
def TraceLocalizedWordHom.sourceImportedRectangles
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceLocalizationWordClass.sourceImportedRectangles hom

/-- Target endpoint rectangles carried by a localized-word hom. -/
def TraceLocalizedWordHom.targetImportedRectangles
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceLocalizationWordClass.targetImportedRectangles hom

/-- Source endpoint count carried by a localized-word hom. -/
def TraceLocalizedWordHom.sourceImportedRectangleCount
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    Nat :=
  TraceLocalizationWordClass.sourceImportedRectangleCount hom

/-- Target endpoint count carried by a localized-word hom. -/
def TraceLocalizedWordHom.targetImportedRectangleCount
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    Nat :=
  TraceLocalizationWordClass.targetImportedRectangleCount hom

/-- Endpoint rectangles carried by a localized-word hom. -/
def TraceLocalizedWordHom.endpointImportedRectangles
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  hom.sourceImportedRectangles ++
    hom.targetImportedRectangles

/-- Endpoint imported-rectangle count carried by a localized-word hom. -/
def TraceLocalizedWordHom.endpointImportedRectangleCount
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    Nat :=
  hom.sourceImportedRectangleCount +
    hom.targetImportedRectangleCount

/-- Source endpoint imported count is the length of the source endpoint rectangle list. -/
theorem TraceLocalizedWordHom.sourceImportedRectangleCount_eq_length
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.sourceImportedRectangleCount =
      hom.sourceImportedRectangles.length :=
  TraceLocalizationWordClass.sourceImportedRectangleCount_eq_length hom

/-- Target endpoint imported count is the length of the target endpoint rectangle list. -/
theorem TraceLocalizedWordHom.targetImportedRectangleCount_eq_length
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.targetImportedRectangleCount =
      hom.targetImportedRectangles.length :=
  TraceLocalizationWordClass.targetImportedRectangleCount_eq_length hom

/-- Endpoint imported count is the length of the endpoint rectangle list. -/
theorem TraceLocalizedWordHom.endpointImportedRectangleCount_eq_length
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.endpointImportedRectangleCount =
      hom.endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length hom

/-- Identity hom source endpoint rectangles are the object's imported rectangles. -/
theorem TraceLocalizedWordHom.id_sourceImportedRectangles
    (object : TraceLocalizedWordObject) :
    (TraceLocalizationWordClass.identity object.underlying).sourceImportedRectangles =
      object.importedRectangles :=
  rfl

/-- Identity hom target endpoint rectangles are the object's imported rectangles. -/
theorem TraceLocalizedWordHom.id_targetImportedRectangles
    (object : TraceLocalizedWordObject) :
    (TraceLocalizationWordClass.identity object.underlying).targetImportedRectangles =
      object.importedRectangles :=
  rfl

/-- Identity hom source endpoint count is the object's imported count. -/
theorem TraceLocalizedWordHom.id_sourceImportedRectangleCount
    (object : TraceLocalizedWordObject) :
    (TraceLocalizationWordClass.identity object.underlying).sourceImportedRectangleCount =
      object.importedRectangleCount :=
  rfl

/-- Identity hom target endpoint count is the object's imported count. -/
theorem TraceLocalizedWordHom.id_targetImportedRectangleCount
    (object : TraceLocalizedWordObject) :
    (TraceLocalizationWordClass.identity object.underlying).targetImportedRectangleCount =
      object.importedRectangleCount :=
  rfl

/-- Identity hom endpoint rectangles are the object's imported rectangles twice. -/
theorem TraceLocalizedWordHom.id_endpointImportedRectangles
    (object : TraceLocalizedWordObject) :
    (TraceLocalizationWordClass.identity object.underlying).endpointImportedRectangles =
      object.importedRectangles ++ object.importedRectangles :=
  rfl

/-- Identity hom endpoint imported count is the object's imported count twice. -/
theorem TraceLocalizedWordHom.id_endpointImportedRectangleCount
    (object : TraceLocalizedWordObject) :
    (TraceLocalizationWordClass.identity object.underlying).endpointImportedRectangleCount =
      object.importedRectangleCount + object.importedRectangleCount :=
  rfl

/-- Composition keeps the left hom source endpoint rectangles. -/
theorem TraceLocalizedWordHom.comp_sourceImportedRectangles
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    (TraceLocalizationWordClass.comp left right).sourceImportedRectangles =
      left.sourceImportedRectangles :=
  TraceLocalizationWordClass.comp_sourceImportedRectangles left right

/-- Composition keeps the right hom target endpoint rectangles. -/
theorem TraceLocalizedWordHom.comp_targetImportedRectangles
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    (TraceLocalizationWordClass.comp left right).targetImportedRectangles =
      right.targetImportedRectangles :=
  TraceLocalizationWordClass.comp_targetImportedRectangles left right

/-- Composition keeps the left hom source endpoint count. -/
theorem TraceLocalizedWordHom.comp_sourceImportedRectangleCount
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    (TraceLocalizationWordClass.comp left right).sourceImportedRectangleCount =
      left.sourceImportedRectangleCount :=
  TraceLocalizationWordClass.comp_sourceImportedRectangleCount left right

/-- Composition keeps the right hom target endpoint count. -/
theorem TraceLocalizedWordHom.comp_targetImportedRectangleCount
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    (TraceLocalizationWordClass.comp left right).targetImportedRectangleCount =
      right.targetImportedRectangleCount :=
  TraceLocalizationWordClass.comp_targetImportedRectangleCount left right

/-- The endpoint rectangles of a composed hom are the left source rectangles followed by right target rectangles. -/
theorem TraceLocalizedWordHom.comp_endpointImportedRectangles
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangles =
      left.sourceImportedRectangles ++
        right.targetImportedRectangles :=
  TraceLocalizationWordClass.comp_endpointImportedRectangles left right

/-- The endpoint imported count of a composed hom is the left source count plus right target count. -/
theorem TraceLocalizedWordHom.comp_endpointImportedRectangleCount
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangleCount =
      left.sourceImportedRectangleCount +
        right.targetImportedRectangleCount :=
  TraceLocalizationWordClass.comp_endpointImportedRectangleCount left right

end AnalyticMotives
end LFunctions
end Boundary
