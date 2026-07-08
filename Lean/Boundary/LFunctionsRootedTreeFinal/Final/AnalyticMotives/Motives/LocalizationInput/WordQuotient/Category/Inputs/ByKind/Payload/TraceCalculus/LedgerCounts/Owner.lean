import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.TraceCalculus.LedgerCounts.Forward.Owner

/-!
# Ledger-count facts for named input arrows by kind

This file gives by-kind names to the fact that endpoint bookkeeping and
rewrite-step counts are counted by the corresponding endpoint certificate
ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
