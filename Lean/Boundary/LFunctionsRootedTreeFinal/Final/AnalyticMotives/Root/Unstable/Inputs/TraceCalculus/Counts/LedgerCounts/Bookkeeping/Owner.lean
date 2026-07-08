import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.TraceCalculus.Counts.LedgerCounts.Bookkeeping.Owner

/-!
# Top-root all-kind unstable input trace-bookkeeping ledger counts

This file mirrors the motive-root endpoint trace-bookkeeping
count-as-certificate-ledger-count facts for hom and inverse arrows of all six
named unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-channel inverse bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement hom bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement inverse bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule hom bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule inverse bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes hom bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes inverse bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini hom bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini inverse bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse bookkeeping count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
