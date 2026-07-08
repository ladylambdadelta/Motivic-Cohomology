import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.Endpoint.Owner

/-!
# Endpoint imported-rectangle payload for unstable cancellation composites

This file exposes endpoint imported-rectangle lists and counts for the
cancellation composites of the six named unstable analytic-motive
localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- Descent-channel unstable inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- Descent-refinement unstable hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- Descent-refinement unstable inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- Descent-schedule unstable hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- Descent-schedule unstable inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- Interval-Stokes unstable hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- Interval-Stokes unstable inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- Interval-Fubini unstable hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- Interval-Fubini unstable inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- Tate-weight-drop unstable hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- Tate-weight-drop unstable inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
