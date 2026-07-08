import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.ImportedRectangles.Endpoint.Owner

/-!
# Endpoint imported-rectangle counts for unstable cancellation composites

This file exposes endpoint imported-rectangle counts for the cancellation
composites of the six named unstable analytic-motive localization
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- Descent-channel unstable inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- Descent-refinement unstable hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- Descent-refinement unstable inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- Descent-schedule unstable hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- Descent-schedule unstable inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- Interval-Stokes unstable hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- Interval-Stokes unstable inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- Interval-Fubini unstable hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- Interval-Fubini unstable inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- Tate-weight-drop unstable hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- Tate-weight-drop unstable inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
