import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Atoms.Payload.Lengths.Owner

/-!
# Payload for localized atom arrows

This file owns the payload surface for one-step localized atom arrows.  The
nested length owner proves the concrete imported-rectangle count invariants;
this owner re-exposes them at the atom payload boundary.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The atom payload surface exposes source-object rectangle counts. -/
theorem TraceLocalizationAtomPayload.localizedSourceObject_importedRectangleCount_eq_length
    (atom : TraceLocalizationAtom) :
    atom.localizedSourceObject.importedRectangleCount =
      atom.localizedSourceObject.importedRectangles.length :=
  TraceLocalizationAtom.localizedSourceObject_importedRectangleCount_eq_length
    atom

/-- The atom payload surface exposes target-object rectangle counts. -/
theorem TraceLocalizationAtomPayload.localizedTargetObject_importedRectangleCount_eq_length
    (atom : TraceLocalizationAtom) :
    atom.localizedTargetObject.importedRectangleCount =
      atom.localizedTargetObject.importedRectangles.length :=
  TraceLocalizationAtom.localizedTargetObject_importedRectangleCount_eq_length
    atom

/-- The atom payload surface exposes localized-arrow endpoint rectangle counts. -/
theorem TraceLocalizationAtomPayload.localizedArrow_endpointImportedRectangleCount_eq_length
    (atom : TraceLocalizationAtom) :
    atom.localizedArrow.endpointImportedRectangleCount =
      atom.localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationAtom.localizedArrow_endpointImportedRectangleCount_eq_length
    atom

/-- The atom payload surface exposes forward-atom endpoint rectangle counts. -/
theorem TraceLocalizationAtomPayload.forward_localizedArrow_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationAtom.forward input).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationAtom.forward_localizedArrow_endpointImportedRectangleCount_eq_length
    input

/-- The atom payload surface exposes inverse-atom endpoint rectangle counts. -/
theorem TraceLocalizationAtomPayload.inverse_localizedArrow_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).localizedArrow.endpointImportedRectangleCount =
      (TraceLocalizationAtom.inverse input).localizedArrow.endpointImportedRectangles.length :=
  TraceLocalizationAtom.inverse_localizedArrow_endpointImportedRectangleCount_eq_length
    input

end AnalyticMotives
end LFunctions
end Boundary
