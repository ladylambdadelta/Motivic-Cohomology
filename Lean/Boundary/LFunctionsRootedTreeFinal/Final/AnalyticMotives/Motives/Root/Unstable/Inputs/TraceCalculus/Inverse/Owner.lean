import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.TraceCalculus.Hom.Owner

/-!
# Root unstable input inverse trace-calculus wrappers
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Descent-refinement unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableDescentRefinementIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Descent-schedule unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableDescentScheduleIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Stokes unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableIntervalStokesIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Interval-Fubini unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Tate-weight-drop unstable inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointTraceBookkeepingCount
    source
    target

/-- Descent-channel unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointRewriteStepCount
    source
    target

/-- Descent-refinement unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableDescentRefinementIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointRewriteStepCount
    source
    target

/-- Descent-schedule unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableDescentScheduleIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointRewriteStepCount
    source
    target

/-- Interval-Stokes unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableIntervalStokesIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointRewriteStepCount
    source
    target

/-- Interval-Fubini unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointRewriteStepCount
    source
    target

/-- Tate-weight-drop unstable inverse endpoint rewrite count is target plus source rewrite count. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_inv_endpointRewriteStepCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.rewriteStepCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointRewriteStepCount
    source
    target

/-- Descent-channel unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentRefinementIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentScheduleIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableIntervalStokesIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentRefinementIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentScheduleIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableIntervalStokesIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
