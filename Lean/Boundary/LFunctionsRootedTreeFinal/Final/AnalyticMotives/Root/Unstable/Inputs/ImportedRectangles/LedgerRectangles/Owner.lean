import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ImportedRectangles.LedgerRectangles.ArrowEndpoints.Owner

/-!
# Top-root all-kind unstable input imported-rectangle ledger lists

This file mirrors the motive-root endpoint imported-rectangle
list-as-certificate-ledger-list surface for hom and inverse arrows of all six
named unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind descent-channel inverse endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind descent-refinement hom endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind descent-refinement inverse endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind descent-schedule hom endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind descent-schedule inverse endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind interval-Stokes hom endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind interval-Stokes inverse endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind interval-Fubini hom endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind interval-Fubini inverse endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse endpoint rectangle ledger extraction. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
