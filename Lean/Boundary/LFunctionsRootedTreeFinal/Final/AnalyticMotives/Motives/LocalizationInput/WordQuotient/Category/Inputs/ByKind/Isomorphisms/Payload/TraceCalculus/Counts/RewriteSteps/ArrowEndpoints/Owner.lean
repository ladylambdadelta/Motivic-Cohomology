import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Owner

/-!
# Rewrite-step arrow-endpoint counts for named localized isomorphisms

This file exposes source and target rewrite-step counts through the hom and
inverse arrows of the named by-kind localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom source rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentChannelForwardArrow_sourceRewriteStepCount
    source
    target

/-- Descent-channel isomorphism hom target rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.descentChannelForwardArrow_targetRewriteStepCount
    source
    target

/-- Descent-channel isomorphism inverse source rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.descentChannelInverseArrow_sourceRewriteStepCount
    source
    target

/-- Descent-channel isomorphism inverse target rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentChannelInverseArrow_targetRewriteStepCount
    source
    target

/-- Descent-refinement isomorphism hom source rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_sourceRewriteStepCount
    source
    target

/-- Descent-refinement isomorphism hom target rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_targetRewriteStepCount
    source
    target

/-- Descent-refinement isomorphism inverse source rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_sourceRewriteStepCount
    source
    target

/-- Descent-refinement isomorphism inverse target rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_targetRewriteStepCount
    source
    target

/-- Descent-schedule isomorphism hom source rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_sourceRewriteStepCount
    source
    target

/-- Descent-schedule isomorphism hom target rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_targetRewriteStepCount
    source
    target

/-- Descent-schedule isomorphism inverse source rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_sourceRewriteStepCount
    source
    target

/-- Descent-schedule isomorphism inverse target rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_targetRewriteStepCount
    source
    target

/-- Interval-Stokes isomorphism hom source rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_sourceRewriteStepCount
    source
    target

/-- Interval-Stokes isomorphism hom target rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_targetRewriteStepCount
    source
    target

/-- Interval-Stokes isomorphism inverse source rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_sourceRewriteStepCount
    source
    target

/-- Interval-Stokes isomorphism inverse target rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_targetRewriteStepCount
    source
    target

/-- Interval-Fubini isomorphism hom source rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_sourceRewriteStepCount
    source
    target

/-- Interval-Fubini isomorphism hom target rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_targetRewriteStepCount
    source
    target

/-- Interval-Fubini isomorphism inverse source rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_sourceRewriteStepCount
    source
    target

/-- Interval-Fubini isomorphism inverse target rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_targetRewriteStepCount
    source
    target

/-- Tate-weight-drop isomorphism hom source rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_sourceRewriteStepCount
    source
    target

/-- Tate-weight-drop isomorphism hom target rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.targetRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_targetRewriteStepCount
    source
    target

/-- Tate-weight-drop isomorphism inverse source rewrite-step count is the input target count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_sourceRewriteStepCount
    source
    target

/-- Tate-weight-drop isomorphism inverse target rewrite-step count is the input source count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.targetRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_targetRewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
