import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.TraceCalculus.Counts.Inverse.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.Bookkeeping.LedgerCounts.Endpoint.Owner

/-!
# By-kind unstable bookkeeping ledger counts

This file exposes endpoint trace-bookkeeping count-as-ledger-count facts for
the six named unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointTraceBookkeepingCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
