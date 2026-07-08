import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.LedgerRectangles.Owner

/-!
# Imported finite-rectangle payload for named localized isomorphisms

This file exposes the concatenated imported finite-rectangle endpoint payload
through the hom and inverse arrows of the named by-kind localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentChannelForwardArrow_endpointImportedRectangles
    source
    target

/-- Descent-channel isomorphism inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentChannelInverseArrow_endpointImportedRectangles
    source
    target

/-- Descent-refinement isomorphism hom endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementForwardArrow_endpointImportedRectangles
    source
    target

/-- Descent-refinement isomorphism inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementInverseArrow_endpointImportedRectangles
    source
    target

/-- Descent-schedule isomorphism hom endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleForwardArrow_endpointImportedRectangles
    source
    target

/-- Descent-schedule isomorphism inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleInverseArrow_endpointImportedRectangles
    source
    target

/-- Interval-Stokes isomorphism hom endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesForwardArrow_endpointImportedRectangles
    source
    target

/-- Interval-Stokes isomorphism inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesInverseArrow_endpointImportedRectangles
    source
    target

/-- Interval-Fubini isomorphism hom endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniForwardArrow_endpointImportedRectangles
    source
    target

/-- Interval-Fubini isomorphism inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniInverseArrow_endpointImportedRectangles
    source
    target

/-- Tate-weight-drop isomorphism hom endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropForwardArrow_endpointImportedRectangles
    source
    target

/-- Tate-weight-drop isomorphism inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropInverseArrow_endpointImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
