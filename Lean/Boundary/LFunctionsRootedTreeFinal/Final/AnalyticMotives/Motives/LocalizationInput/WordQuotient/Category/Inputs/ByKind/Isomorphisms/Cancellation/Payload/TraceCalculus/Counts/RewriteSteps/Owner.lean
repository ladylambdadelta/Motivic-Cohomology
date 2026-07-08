import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.Counts.RewriteSteps.ArrowEndpoints.Owner

/-!
# Endpoint rewrite-step counts for named cancellation composites

This file specializes the generic input-cancellation endpoint rewrite-step
count facts to the six named localization-input constructors.  Source and
target endpoint count facts live in the `ArrowEndpoints` child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation endpoint rewrite count is doubled source rewrite count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointRewriteStepCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation endpoint rewrite count is doubled target rewrite count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointRewriteStepCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation endpoint rewrite count is doubled source rewrite count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointRewriteStepCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation endpoint rewrite count is doubled target rewrite count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointRewriteStepCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation endpoint rewrite count is doubled source rewrite count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointRewriteStepCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation endpoint rewrite count is doubled target rewrite count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointRewriteStepCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation endpoint rewrite count is doubled source rewrite count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointRewriteStepCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation endpoint rewrite count is doubled target rewrite count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointRewriteStepCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation endpoint rewrite count is doubled source rewrite count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointRewriteStepCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation endpoint rewrite count is doubled target rewrite count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointRewriteStepCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation endpoint rewrite count is doubled source rewrite count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointRewriteStepCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation endpoint rewrite count is doubled target rewrite count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointRewriteStepCount
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
