import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.LedgerCounts.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.LedgerCounts.Owner

/-!
# By-kind unstable imported-rectangle ledger counts

This file exposes endpoint imported-rectangle count-as-ledger-count facts for
the six named unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
