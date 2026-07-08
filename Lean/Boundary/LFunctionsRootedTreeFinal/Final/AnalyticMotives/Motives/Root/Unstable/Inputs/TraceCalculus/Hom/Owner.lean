import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.TraceCalculus.CertificateLedgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.TraceCalculus.Counts.Owner

/-!
# Root unstable input hom trace-calculus wrappers
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Descent-refinement unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableDescentRefinementIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Descent-schedule unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableDescentScheduleIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Stokes unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableIntervalStokesIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Fubini unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Tate-weight-drop unstable hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointTraceBookkeepingCount
    source
    target

/-- Descent-channel unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointRewriteStepCount
    source
    target

/-- Descent-refinement unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableDescentRefinementIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointRewriteStepCount
    source
    target

/-- Descent-schedule unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableDescentScheduleIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointRewriteStepCount
    source
    target

/-- Interval-Stokes unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableIntervalStokesIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointRewriteStepCount
    source
    target

/-- Interval-Fubini unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointRewriteStepCount
    source
    target

/-- Tate-weight-drop unstable hom endpoint rewrite count is source plus target rewrite count. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointRewriteStepCount
    source
    target

/-- Descent-channel unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentRefinementIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentScheduleIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableIntervalStokesIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentRefinementIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentScheduleIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableIntervalStokesIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
