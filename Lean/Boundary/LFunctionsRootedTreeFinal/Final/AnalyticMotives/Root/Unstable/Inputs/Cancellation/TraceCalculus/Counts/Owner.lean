import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.Cancellation.TraceCalculus.Counts.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.TraceCalculus.Counts.Owner

/-!
# Top-root cancellation trace-calculus counts

This file mirrors the motive-root endpoint trace-bookkeeping and rewrite-step
count boundary at the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root descent-channel hom-inverse cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Top-root descent-channel inverse-hom cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Top-root descent-channel hom-inverse cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Top-root descent-channel inverse-hom cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Top-root descent-refinement hom-inverse cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Top-root descent-refinement inverse-hom cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Top-root descent-refinement hom-inverse cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Top-root descent-refinement inverse-hom cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Top-root descent-schedule hom-inverse cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Top-root descent-schedule inverse-hom cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Top-root descent-schedule hom-inverse cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Top-root descent-schedule inverse-hom cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Top-root interval-Stokes hom-inverse cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Top-root interval-Stokes inverse-hom cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Top-root interval-Stokes hom-inverse cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Top-root interval-Stokes inverse-hom cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Top-root interval-Fubini hom-inverse cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Top-root interval-Fubini inverse-hom cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Top-root interval-Fubini hom-inverse cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Top-root interval-Fubini inverse-hom cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Top-root Tate-weight-drop hom-inverse cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Top-root Tate-weight-drop inverse-hom cancellation endpoint bookkeeping count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Top-root Tate-weight-drop hom-inverse cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Top-root Tate-weight-drop inverse-hom cancellation endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
