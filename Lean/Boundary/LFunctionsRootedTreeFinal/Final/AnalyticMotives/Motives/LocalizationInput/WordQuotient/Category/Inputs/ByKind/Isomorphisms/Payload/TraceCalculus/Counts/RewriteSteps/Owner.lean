import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.RewriteSteps.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.TraceCalculus.Owner

/-!
# Rewrite-step counts for named localized isomorphisms

This file exposes concatenated endpoint rewrite-step counts through the hom and
inverse arrows of the named by-kind localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointRewriteStepCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel isomorphism inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointRewriteStepCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement isomorphism hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointRewriteStepCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement isomorphism inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointRewriteStepCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule isomorphism hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointRewriteStepCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule isomorphism inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointRewriteStepCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes isomorphism hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointRewriteStepCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes isomorphism inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointRewriteStepCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini isomorphism hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointRewriteStepCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini isomorphism inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointRewriteStepCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop isomorphism hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointRewriteStepCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop isomorphism inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointRewriteStepCount
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
