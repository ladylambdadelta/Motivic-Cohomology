import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.TraceCalculus.Counts.Inverse.Owner

/-!
# Root all-kind unstable input trace-bookkeeping counts

This file exposes endpoint trace-bookkeeping count formulas for hom and inverse
arrows of all six named unstable localization isomorphisms at the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- By-kind descent-channel inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- By-kind descent-refinement hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- By-kind descent-refinement inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- By-kind descent-schedule hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- By-kind descent-schedule inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- By-kind interval-Stokes hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- By-kind interval-Stokes inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- By-kind interval-Fubini hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- By-kind interval-Fubini inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- By-kind Tate-weight-drop hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- By-kind Tate-weight-drop inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointTraceBookkeepingCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
