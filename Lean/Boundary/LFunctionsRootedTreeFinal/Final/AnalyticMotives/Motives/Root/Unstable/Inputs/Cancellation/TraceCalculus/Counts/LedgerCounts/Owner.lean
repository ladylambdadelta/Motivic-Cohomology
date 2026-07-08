import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.TraceCalculus.Counts.LedgerCounts.Bookkeeping.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.TraceCalculus.Counts.LedgerCounts.RewriteSteps.Owner

/-!
# Motive-root cancellation trace-calculus ledger counts

This file is the motive-root boundary for endpoint count-as-ledger-count facts
carried by the six by-kind unstable cancellation composites.

The imported owners prove that endpoint trace-bookkeeping and rewrite-step
counts of the hom-inverse and inverse-hom cancellation composites are counted
by the corresponding endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root descent-channel hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-channel inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-channel hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-channel inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-refinement hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-refinement inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-refinement hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-refinement inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-schedule hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-schedule inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-schedule hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root descent-schedule inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root interval-Stokes hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root interval-Stokes inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root interval-Stokes hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root interval-Stokes inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root interval-Fubini hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root interval-Fubini inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root interval-Fubini hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root interval-Fubini inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root Tate-weight-drop hom-inverse cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root Tate-weight-drop inverse-hom cancellation bookkeeping count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Motive-root Tate-weight-drop hom-inverse cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Motive-root Tate-weight-drop inverse-hom cancellation rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
