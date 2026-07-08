import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.TraceCalculus.CertificateLedgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.TraceCalculus.Counts.Owner

/-!
# Top-level unstable input hom trace-calculus wrappers
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes descent-channel unstable bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes descent-refinement unstable bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableDescentRefinementIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentRefinementIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes descent-schedule unstable bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableDescentScheduleIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentScheduleIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes interval-Stokes unstable bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableIntervalStokesIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableIntervalStokesIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes interval-Fubini unstable bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes Tate-weight-drop unstable bookkeeping counts. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- The analytic-motives root exposes descent-channel unstable rewrite counts. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointRewriteStepCount
    source
    target

/-- The analytic-motives root exposes descent-refinement unstable rewrite counts. -/
theorem AnalyticMotivesRoot.unstableDescentRefinementIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentRefinementIso_hom_endpointRewriteStepCount
    source
    target

/-- The analytic-motives root exposes descent-schedule unstable rewrite counts. -/
theorem AnalyticMotivesRoot.unstableDescentScheduleIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentScheduleIso_hom_endpointRewriteStepCount
    source
    target

/-- The analytic-motives root exposes interval-Stokes unstable rewrite counts. -/
theorem AnalyticMotivesRoot.unstableIntervalStokesIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableIntervalStokesIso_hom_endpointRewriteStepCount
    source
    target

/-- The analytic-motives root exposes interval-Fubini unstable rewrite counts. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointRewriteStepCount
    source
    target

/-- The analytic-motives root exposes Tate-weight-drop unstable rewrite counts. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointRewriteStepCount
    source
    target

/-- The root exposes descent-channel unstable bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-refinement unstable bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentRefinementIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentRefinementIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-schedule unstable bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentScheduleIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableDescentScheduleIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes interval-Stokes unstable bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableIntervalStokesIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableIntervalStokesIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes interval-Fubini unstable bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes Tate-weight-drop unstable bookkeeping ledger counts. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-channel unstable rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-refinement unstable rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentRefinementIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentRefinementIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-schedule unstable rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentScheduleIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableDescentScheduleIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes interval-Stokes unstable rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableIntervalStokesIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableIntervalStokesIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes interval-Fubini unstable rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes Tate-weight-drop unstable rewrite-step ledger counts. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
