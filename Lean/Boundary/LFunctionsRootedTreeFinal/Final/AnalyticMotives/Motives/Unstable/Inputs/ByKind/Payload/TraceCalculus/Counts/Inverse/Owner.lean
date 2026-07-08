import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.TraceCalculus.Counts.Owner

/-!
# By-kind unstable inverse trace-calculus counts

This file exposes endpoint trace-bookkeeping and rewrite-step counts for the
inverse arrows of the six named unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Descent-refinement unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Descent-schedule unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Stokes unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Fubini unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Tate-weight-drop unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Descent-channel unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointRewriteStepCount
    source
    target

/-- Descent-refinement unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointRewriteStepCount
    source
    target

/-- Descent-schedule unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointRewriteStepCount
    source
    target

/-- Interval-Stokes unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointRewriteStepCount
    source
    target

/-- Interval-Fubini unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointRewriteStepCount
    source
    target

/-- Tate-weight-drop unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointRewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
