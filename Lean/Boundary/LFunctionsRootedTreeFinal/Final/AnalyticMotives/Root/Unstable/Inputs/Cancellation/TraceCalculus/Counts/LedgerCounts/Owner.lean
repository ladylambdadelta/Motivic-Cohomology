import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.TraceCalculus.Counts.LedgerCounts.Owner

/-!
# Top-root cancellation trace-calculus ledger counts

This file mirrors the motive-root endpoint trace-calculus count-as-ledger-count
boundary at the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root descent-channel hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-channel inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-channel hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-channel inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-refinement hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-refinement inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-refinement hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-refinement inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-schedule hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-schedule inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-schedule hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root descent-schedule inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root interval-Stokes hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root interval-Stokes inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root interval-Stokes hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root interval-Stokes inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root interval-Fubini hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root interval-Fubini inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root interval-Fubini hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root interval-Fubini inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root Tate-weight-drop hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root Tate-weight-drop inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Top-root Tate-weight-drop hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Top-root Tate-weight-drop inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
