import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Owner

/-!
# By-kind unstable imported-rectangle payload

This file exposes endpoint imported finite-rectangle payload for the six named
unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom endpoint rectangles are source followed by target. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointImportedRectangles
    source
    target

/-- Descent-channel unstable inverse endpoint rectangles are target followed by source. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointImportedRectangles
    source
    target

/-- Descent-refinement unstable hom endpoint rectangles are source followed by target. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointImportedRectangles
    source
    target

/-- Descent-refinement unstable inverse endpoint rectangles are target followed by source. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointImportedRectangles
    source
    target

/-- Descent-schedule unstable hom endpoint rectangles are source followed by target. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointImportedRectangles
    source
    target

/-- Descent-schedule unstable inverse endpoint rectangles are target followed by source. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointImportedRectangles
    source
    target

/-- Interval-Stokes unstable hom endpoint rectangles are source followed by target. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointImportedRectangles
    source
    target

/-- Interval-Stokes unstable inverse endpoint rectangles are target followed by source. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointImportedRectangles
    source
    target

/-- Interval-Fubini unstable hom endpoint rectangles are source followed by target. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointImportedRectangles
    source
    target

/-- Interval-Fubini unstable inverse endpoint rectangles are target followed by source. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointImportedRectangles
    source
    target

/-- Tate-weight-drop unstable hom endpoint rectangles are source followed by target. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointImportedRectangles
    source
    target

/-- Tate-weight-drop unstable inverse endpoint rectangles are target followed by source. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
