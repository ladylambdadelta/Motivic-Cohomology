import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.TraceCalculus.Counts.Inverse.Owner

/-!
# Root all-kind unstable input rewrite-step counts

This file exposes endpoint rewrite-step count formulas for hom and inverse
arrows of all six named unstable localization isomorphisms at the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointRewriteStepCount
    source
    target

/-- By-kind descent-channel inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointRewriteStepCount
    source
    target

/-- By-kind descent-refinement hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointRewriteStepCount
    source
    target

/-- By-kind descent-refinement inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointRewriteStepCount
    source
    target

/-- By-kind descent-schedule hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointRewriteStepCount
    source
    target

/-- By-kind descent-schedule inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointRewriteStepCount
    source
    target

/-- By-kind interval-Stokes hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointRewriteStepCount
    source
    target

/-- By-kind interval-Stokes inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointRewriteStepCount
    source
    target

/-- By-kind interval-Fubini hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointRewriteStepCount
    source
    target

/-- By-kind interval-Fubini inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointRewriteStepCount
    source
    target

/-- By-kind Tate-weight-drop hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointRewriteStepCount
    source
    target

/-- By-kind Tate-weight-drop inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointRewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
