import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.TraceCalculus.Counts.LedgerCounts.Bookkeeping.Owner

/-!
# Root all-kind unstable input trace-bookkeeping ledger counts

This file exposes endpoint trace-bookkeeping count-as-certificate-ledger-count
facts for hom and inverse arrows of all six named unstable localization
isomorphisms at the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-channel inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-refinement hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-refinement inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-schedule hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-schedule inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Stokes hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Stokes inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Fubini hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Fubini inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind Tate-weight-drop hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- By-kind Tate-weight-drop inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
