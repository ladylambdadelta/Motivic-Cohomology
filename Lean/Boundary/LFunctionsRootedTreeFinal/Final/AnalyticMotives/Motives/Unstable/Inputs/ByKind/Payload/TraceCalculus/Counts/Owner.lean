import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.Owner

/-!
# By-kind unstable trace-calculus counts

This file exposes endpoint trace-bookkeeping and rewrite-step counts for the
hom arrows of the six named unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Descent-refinement unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Descent-schedule unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Stokes unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Fubini unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Tate-weight-drop unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Descent-channel unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointRewriteStepCount
    source
    target

/-- Descent-refinement unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointRewriteStepCount
    source
    target

/-- Descent-schedule unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointRewriteStepCount
    source
    target

/-- Interval-Stokes unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointRewriteStepCount
    source
    target

/-- Interval-Fubini unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointRewriteStepCount
    source
    target

/-- Tate-weight-drop unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointRewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
