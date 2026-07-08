import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.LedgerRectangles.ArrowEndpoints.Owner

/-!
# Root all-kind unstable input imported-rectangle ledger lists

This file exposes endpoint imported-rectangle list-as-certificate-ledger-list
facts for hom and inverse arrows of all six named unstable localization
isomorphisms at the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind descent-channel inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind descent-refinement hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind descent-refinement inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind descent-schedule hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind descent-schedule inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind interval-Stokes hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind interval-Stokes inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind interval-Fubini hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind interval-Fubini inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind Tate-weight-drop hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- By-kind Tate-weight-drop inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
