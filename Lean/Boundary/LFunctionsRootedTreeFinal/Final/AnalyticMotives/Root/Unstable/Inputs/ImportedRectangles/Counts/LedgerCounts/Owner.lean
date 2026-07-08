import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ImportedRectangles.Counts.LedgerCounts.ArrowEndpoints.Owner

/-!
# Top-root all-kind unstable input imported-rectangle ledger counts

This file mirrors the motive-root endpoint imported-rectangle
count-as-certificate-ledger-count surface for hom and inverse arrows of all six
named unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-channel inverse endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement hom endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement inverse endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule hom endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule inverse endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes hom endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes inverse endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini hom endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini inverse endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse endpoint rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
