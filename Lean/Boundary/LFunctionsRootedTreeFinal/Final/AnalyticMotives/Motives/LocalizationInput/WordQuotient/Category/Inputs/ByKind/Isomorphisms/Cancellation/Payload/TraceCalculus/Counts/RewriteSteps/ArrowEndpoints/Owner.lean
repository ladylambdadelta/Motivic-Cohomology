import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.TraceCalculus.Owner

/-!
# Endpoint rewrite-step counts for named cancellation composites

This file specializes the generic input-cancellation source and target
rewrite-step count facts to the six named localization-input constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation source rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoHomInv.sourceRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel hom-inverse cancellation target rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoHomInv.targetRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation source rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoInvHom.sourceRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation target rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoInvHom.targetRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation source rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoHomInv.sourceRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement hom-inverse cancellation target rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoHomInv.targetRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation source rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoInvHom.sourceRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation target rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoInvHom.targetRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation source rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoHomInv.sourceRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule hom-inverse cancellation target rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoHomInv.targetRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation source rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoInvHom.sourceRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation target rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoInvHom.targetRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation source rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoHomInv.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes hom-inverse cancellation target rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoHomInv.targetRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation source rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoInvHom.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation target rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoInvHom.targetRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation source rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoHomInv.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini hom-inverse cancellation target rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoHomInv.targetRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation source rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoInvHom.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation target rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoInvHom.targetRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation source rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoHomInv.sourceRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop hom-inverse cancellation target rewrite count is the source endpoint count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoHomInv.targetRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation source rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoInvHom.sourceRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation target rewrite count is the target endpoint count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoInvHom.targetRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
