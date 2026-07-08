import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Payload.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Owner

/-!
# Payload in the unstable analytic-motive envelope

This file exposes the analytic payload already carried by the localized-word
category through the current unstable analytic-motive names.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Imported rectangles carried by an unstable analytic motive. -/
def TraceUnstableAnalyticMotive.importedRectangles
    (object : TraceUnstableAnalyticMotive) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceLocalizedWordObject.importedRectangles object

/-- Imported-rectangle count carried by an unstable analytic motive. -/
def TraceUnstableAnalyticMotive.importedRectangleCount
    (object : TraceUnstableAnalyticMotive) :
    Nat :=
  TraceLocalizedWordObject.importedRectangleCount object

/-- Imported-rectangle count is the length of the imported rectangle list. -/
theorem TraceUnstableAnalyticMotive.importedRectangleCount_eq_length
    (object : TraceUnstableAnalyticMotive) :
    object.importedRectangleCount =
      object.importedRectangles.length :=
  TraceLocalizedWordObject.importedRectangleCount_eq_length
    object

/-- Wrapping a trace object preserves imported rectangles in the unstable envelope. -/
theorem TraceUnstableAnalyticMotive.ofTraceObject_importedRectangles
    (object : TraceCorQObject) :
    (TraceUnstableAnalyticMotive.ofTraceObject object).importedRectangles =
      object.importedRectangles :=
  TraceLocalizedWordObject.ofTraceObject_importedRectangles
    object

/-- Wrapping a trace object preserves imported-rectangle count in the unstable envelope. -/
theorem TraceUnstableAnalyticMotive.ofTraceObject_importedRectangleCount
    (object : TraceCorQObject) :
    (TraceUnstableAnalyticMotive.ofTraceObject object).importedRectangleCount =
      object.importedRectangleCount :=
  TraceLocalizedWordObject.ofTraceObject_importedRectangleCount
    object

/-- Source endpoint rectangles carried by an unstable analytic-motive hom. -/
def TraceUnstableAnalyticMotiveHom.sourceImportedRectangles
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceLocalizedWordHom.sourceImportedRectangles hom

/-- Target endpoint rectangles carried by an unstable analytic-motive hom. -/
def TraceUnstableAnalyticMotiveHom.targetImportedRectangles
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceLocalizedWordHom.targetImportedRectangles hom

/-- Source endpoint imported-rectangle count carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.sourceImportedRectangleCount
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    Nat :=
  TraceLocalizedWordHom.sourceImportedRectangleCount hom

/-- Target endpoint imported-rectangle count carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.targetImportedRectangleCount
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    Nat :=
  TraceLocalizedWordHom.targetImportedRectangleCount hom

/-- Source endpoint count is the length of source endpoint rectangles. -/
theorem TraceUnstableAnalyticMotiveHom.sourceImportedRectangleCount_eq_length
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.sourceImportedRectangleCount =
      hom.sourceImportedRectangles.length :=
  TraceLocalizedWordHom.sourceImportedRectangleCount_eq_length
    hom

/-- Target endpoint count is the length of target endpoint rectangles. -/
theorem TraceUnstableAnalyticMotiveHom.targetImportedRectangleCount_eq_length
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.targetImportedRectangleCount =
      hom.targetImportedRectangles.length :=
  TraceLocalizedWordHom.targetImportedRectangleCount_eq_length
    hom

/-- Identity hom source endpoint rectangles are the object's imported rectangles. -/
theorem TraceUnstableAnalyticMotiveHom.id_sourceImportedRectangles
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).sourceImportedRectangles =
      object.importedRectangles :=
  TraceLocalizedWordHom.id_sourceImportedRectangles
    object

/-- Identity hom target endpoint rectangles are the object's imported rectangles. -/
theorem TraceUnstableAnalyticMotiveHom.id_targetImportedRectangles
    (object : TraceUnstableAnalyticMotive) :
    (TraceLocalizationWordClass.identity object.underlying).targetImportedRectangles =
      object.importedRectangles :=
  TraceLocalizedWordHom.id_targetImportedRectangles
    object

end AnalyticMotives
end LFunctions
end Boundary
