import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.Counts.Bookkeeping.Owner

/-!
# Endpoint trace-bookkeeping counts for unstable cancellation composites

This file exposes endpoint trace-bookkeeping counts for cancellation composites
of the six named unstable analytic-motive localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Descent-channel unstable inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Descent-refinement unstable hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Descent-refinement unstable inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Descent-schedule unstable hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Descent-schedule unstable inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Stokes unstable hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Stokes unstable inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Fubini unstable hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Fubini unstable inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Tate-weight-drop unstable hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Tate-weight-drop unstable inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
