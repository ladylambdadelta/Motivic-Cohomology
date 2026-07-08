import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.LedgerCounts.ArrowEndpoints.Owner

/-!
# Root all-kind unstable input imported-rectangle ledger counts

This file exposes endpoint imported-rectangle count-as-certificate-ledger-count
facts for hom and inverse arrows of all six named unstable localization
isomorphisms at the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-channel inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-refinement hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-refinement inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-schedule hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-schedule inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Stokes hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Stokes inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Fubini hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Fubini inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind Tate-weight-drop hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind Tate-weight-drop inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
