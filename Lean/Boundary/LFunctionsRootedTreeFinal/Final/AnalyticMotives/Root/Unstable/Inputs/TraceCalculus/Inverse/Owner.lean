import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.TraceCalculus.Hom.Owner

/-!
# Top-level unstable input inverse trace-calculus wrappers
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes descent-channel inverse bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentChannelIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes descent-refinement inverse bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableDescentRefinementIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentRefinementIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes descent-schedule inverse bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableDescentScheduleIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentScheduleIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes interval-Stokes inverse bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableIntervalStokesIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableIntervalStokesIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes interval-Fubini inverse bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes Tate-weight-drop inverse bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableTateWeightDropIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes descent-channel inverse rewrite counts. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentChannelIso_inv_endpointRewriteStepCount
    source
    target

/-- The analytic-motives root exposes descent-refinement inverse rewrite counts. -/
theorem AnalyticMotivesRoot.unstableDescentRefinementIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentRefinementIso_inv_endpointRewriteStepCount
    source
    target

/-- The analytic-motives root exposes descent-schedule inverse rewrite counts. -/
theorem AnalyticMotivesRoot.unstableDescentScheduleIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentScheduleIso_inv_endpointRewriteStepCount
    source
    target

/-- The analytic-motives root exposes interval-Stokes inverse rewrite counts. -/
theorem AnalyticMotivesRoot.unstableIntervalStokesIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableIntervalStokesIso_inv_endpointRewriteStepCount
    source
    target

/-- The analytic-motives root exposes interval-Fubini inverse rewrite counts. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_inv_endpointRewriteStepCount
    source
    target

/-- The analytic-motives root exposes Tate-weight-drop inverse rewrite counts. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableTateWeightDropIso_inv_endpointRewriteStepCount
    source
    target

/-- The root exposes descent-channel inverse bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentChannelIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-refinement inverse bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentRefinementIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentRefinementIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-schedule inverse bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentScheduleIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentScheduleIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes interval-Stokes inverse bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableIntervalStokesIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableIntervalStokesIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes interval-Fubini inverse bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes Tate-weight-drop inverse bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableTateWeightDropIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-channel inverse rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentChannelIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-refinement inverse rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentRefinementIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentRefinementIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-schedule inverse rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentScheduleIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentScheduleIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes interval-Stokes inverse rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableIntervalStokesIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableIntervalStokesIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes interval-Fubini inverse rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes Tate-weight-drop inverse rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableTateWeightDropIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
