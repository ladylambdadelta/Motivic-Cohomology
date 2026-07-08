import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.TraceCalculus.Counts.RewriteSteps.Owner

/-!
# Top-root all-kind unstable input rewrite-step counts

This file mirrors the motive-root endpoint rewrite-step count formulas for hom
and inverse arrows of all six named unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind descent-channel inverse endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind descent-refinement hom endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind descent-refinement inverse endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind descent-schedule hom endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind descent-schedule inverse endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind interval-Stokes hom endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind interval-Stokes inverse endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind interval-Fubini hom endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind interval-Fubini inverse endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointRewriteStepCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse endpoint rewrite counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointRewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
