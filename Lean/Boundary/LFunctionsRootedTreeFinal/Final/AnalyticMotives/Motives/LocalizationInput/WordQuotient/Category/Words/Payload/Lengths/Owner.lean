import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Words.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Lengths.Owner

/-!
# Localized word-arrow payload length facts

This file owns imported-rectangle length invariants for localized-word category
objects and arrows represented by formal localization words.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A localized word source object has count equal to rectangle-list length. -/
theorem TraceLocalizationWord.localizedSourceObject_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.localizedSourceObject.importedRectangleCount =
      word.localizedSourceObject.importedRectangles.length :=
  TraceLocalizedWordObject.importedRectangleCount_eq_length
    word.localizedSourceObject

/-- A localized word target object has count equal to rectangle-list length. -/
theorem TraceLocalizationWord.localizedTargetObject_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.localizedTargetObject.importedRectangleCount =
      word.localizedTargetObject.importedRectangles.length :=
  TraceLocalizedWordObject.importedRectangleCount_eq_length
    word.localizedTargetObject

/-- A localized word arrow endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.localizedArrow_endpointImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.localizedArrow.endpointImportedRectangleCount =
      word.localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizedWordHom.endpointImportedRectangleCount_eq_length
    word.localizedArrow

/-- The identity localized word arrow endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.localizedArrow_identity_endpointImportedRectangleCount_eq_length
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.identity object).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.identity object)

/-- A one-atom localized word arrow endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.localizedArrow_ofAtom_endpointImportedRectangleCount_eq_length
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.ofAtom atom).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.ofAtom atom)

/-- A forward-input localized word arrow endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.localizedArrow_ofInputForward_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputForward input).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.ofInputForward input).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.ofInputForward input)

/-- An inverse-input localized word arrow endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.localizedArrow_ofInputInverse_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputInverse input).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.ofInputInverse input).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.ofInputInverse input)

/-- A concatenated localized word arrow endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.localizedArrow_comp_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.comp left right).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.comp left right)

end AnalyticMotives
end LFunctions
end Boundary
