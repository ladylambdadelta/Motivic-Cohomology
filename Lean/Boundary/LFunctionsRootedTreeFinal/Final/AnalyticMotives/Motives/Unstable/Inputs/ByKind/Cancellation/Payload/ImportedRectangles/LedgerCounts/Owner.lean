import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.ImportedRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.LedgerCounts.Endpoint.Owner

/-!
# Endpoint imported-rectangle ledger counts for unstable cancellation composites

This file exposes endpoint imported-rectangle count-as-ledger-count facts for
the cancellation composites of the six named unstable analytic-motive
localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom-inverse cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable inverse-hom cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable hom-inverse cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable inverse-hom cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable hom-inverse cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable inverse-hom cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable hom-inverse cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable inverse-hom cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable hom-inverse cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable inverse-hom cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable hom-inverse cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable inverse-hom cancellation endpoint count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
