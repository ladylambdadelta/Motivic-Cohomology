import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.Counts.RewriteSteps.Owner

/-!
# Endpoint rewrite-step counts for unstable cancellation composites

This file exposes endpoint rewrite-step counts for cancellation composites of
the six named unstable analytic-motive localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Descent-channel unstable inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Descent-refinement unstable hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Descent-refinement unstable inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Descent-schedule unstable hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Descent-schedule unstable inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Interval-Stokes unstable hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Interval-Stokes unstable inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Interval-Fubini unstable hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Interval-Fubini unstable inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Tate-weight-drop unstable hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Tate-weight-drop unstable inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
