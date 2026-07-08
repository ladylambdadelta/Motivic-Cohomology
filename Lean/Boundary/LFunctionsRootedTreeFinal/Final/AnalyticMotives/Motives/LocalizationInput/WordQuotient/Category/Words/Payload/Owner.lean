import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Words.Payload.Lengths.Owner

/-!
# Payload for localized word arrows

This file owns the payload surface for localized arrows represented by formal
localization words.  The nested length owner proves the imported-rectangle
count invariants; this owner re-exposes them at the word payload boundary.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The word payload surface exposes source-object rectangle counts. -/
theorem TraceLocalizationWordPayload.localizedSourceObject_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.localizedSourceObject.importedRectangleCount =
      word.localizedSourceObject.importedRectangles.length :=
  TraceLocalizationWord.localizedSourceObject_importedRectangleCount_eq_length
    word

/-- The word payload surface exposes target-object rectangle counts. -/
theorem TraceLocalizationWordPayload.localizedTargetObject_importedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.localizedTargetObject.importedRectangleCount =
      word.localizedTargetObject.importedRectangles.length :=
  TraceLocalizationWord.localizedTargetObject_importedRectangleCount_eq_length
    word

/-- The word payload surface exposes localized-arrow endpoint rectangle counts. -/
theorem TraceLocalizationWordPayload.localizedArrow_endpointImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.localizedArrow.endpointImportedRectangleCount =
      word.localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_endpointImportedRectangleCount_eq_length
    word

/-- The word payload surface exposes identity-arrow endpoint rectangle counts. -/
theorem TraceLocalizationWordPayload.localizedArrow_identity_endpointImportedRectangleCount_eq_length
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.identity object).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_identity_endpointImportedRectangleCount_eq_length
    object

/-- The word payload surface exposes one-atom arrow endpoint rectangle counts. -/
theorem TraceLocalizationWordPayload.localizedArrow_ofAtom_endpointImportedRectangleCount_eq_length
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.ofAtom atom).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_ofAtom_endpointImportedRectangleCount_eq_length
    atom

/-- The word payload surface exposes forward-input arrow endpoint rectangle counts. -/
theorem TraceLocalizationWordPayload.localizedArrow_ofInputForward_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputForward input).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.ofInputForward input).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_ofInputForward_endpointImportedRectangleCount_eq_length
    input

/-- The word payload surface exposes inverse-input arrow endpoint rectangle counts. -/
theorem TraceLocalizationWordPayload.localizedArrow_ofInputInverse_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputInverse input).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.ofInputInverse input).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_ofInputInverse_endpointImportedRectangleCount_eq_length
    input

/-- The word payload surface exposes composite-arrow endpoint rectangle counts. -/
theorem TraceLocalizationWordPayload.localizedArrow_comp_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationWord.comp left right).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationWord.localizedArrow_comp_endpointImportedRectangleCount_eq_length
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
