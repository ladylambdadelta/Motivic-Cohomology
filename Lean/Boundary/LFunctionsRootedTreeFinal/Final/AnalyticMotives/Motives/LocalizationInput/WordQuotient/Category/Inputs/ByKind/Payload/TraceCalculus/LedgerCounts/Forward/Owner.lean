import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.TraceCalculus.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.TraceCalculus.Counts.LedgerCounts.Owner

/-!
# Forward-arrow ledger-count facts for named input arrows by kind

This file gives by-kind names to the fact that forward-arrow endpoint
bookkeeping and rewrite-step counts are counted by the corresponding endpoint
certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel forward source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel forward target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel forward target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
