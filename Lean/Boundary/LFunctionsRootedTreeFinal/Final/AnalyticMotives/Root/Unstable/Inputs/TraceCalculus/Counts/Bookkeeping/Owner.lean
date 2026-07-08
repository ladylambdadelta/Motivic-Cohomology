import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.TraceCalculus.Counts.Bookkeeping.Owner

/-!
# Top-root all-kind unstable input trace-bookkeeping counts

This file mirrors the motive-root endpoint trace-bookkeeping count formulas for
hom and inverse arrows of all six named unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind descent-channel inverse endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind descent-refinement hom endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind descent-refinement inverse endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind descent-schedule hom endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind descent-schedule inverse endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind interval-Stokes hom endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind interval-Stokes inverse endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind interval-Fubini hom endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind interval-Fubini inverse endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse endpoint bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointTraceBookkeepingCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
