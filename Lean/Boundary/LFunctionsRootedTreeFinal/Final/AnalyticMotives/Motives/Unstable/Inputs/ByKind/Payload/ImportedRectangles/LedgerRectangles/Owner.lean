import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.LedgerRectangles.ArrowEndpoints.Owner

/-!
# By-kind unstable imported-rectangle ledger lists

This file exposes endpoint imported-rectangle list-as-ledger-list facts for
the six named unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-channel unstable inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement unstable hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement unstable inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule unstable hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule unstable inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes unstable hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes unstable inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini unstable hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini unstable inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop unstable hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop unstable inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
