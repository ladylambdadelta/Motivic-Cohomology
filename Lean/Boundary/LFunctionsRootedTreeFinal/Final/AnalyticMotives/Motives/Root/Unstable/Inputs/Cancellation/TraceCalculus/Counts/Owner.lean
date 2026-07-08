import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.TraceCalculus.Counts.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.TraceCalculus.Counts.Bookkeeping.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.TraceCalculus.Counts.RewriteSteps.Owner

/-!
# Motive-root cancellation trace-calculus counts

This file is the motive-root boundary for endpoint trace-bookkeeping and
rewrite-step count payload carried by the six by-kind unstable cancellation
composites.

The imported owners prove the concrete count formulas for hom-inverse and
inverse-hom cancellation composites and the ledger-count comparisons for those
counts.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root descent-channel hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root descent-channel inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root descent-channel hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Motive-root descent-channel inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Motive-root descent-refinement hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root descent-refinement inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root descent-refinement hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Motive-root descent-refinement inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Motive-root descent-schedule hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root descent-schedule inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root descent-schedule hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Motive-root descent-schedule inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Motive-root interval-Stokes hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root interval-Stokes inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root interval-Stokes hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Motive-root interval-Stokes inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Motive-root interval-Fubini hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root interval-Fubini inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root interval-Fubini hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Motive-root interval-Fubini inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

/-- Motive-root Tate-weight-drop hom-inverse cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root Tate-weight-drop inverse-hom cancellation endpoint bookkeeping count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointTraceBookkeepingCount
    source
    target

/-- Motive-root Tate-weight-drop hom-inverse cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointRewriteStepCount
    source
    target

/-- Motive-root Tate-weight-drop inverse-hom cancellation endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointRewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
