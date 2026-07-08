import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.ImportedRectangles.Endpoint.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.LedgerRectangles.Endpoint.Owner

/-!
# Endpoint imported-rectangle ledger lists for unstable cancellation composites

This file exposes endpoint imported-rectangle list-as-ledger-list facts for the
cancellation composites of the six named unstable analytic-motive localization
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-channel unstable inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement unstable hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement unstable inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule unstable hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule unstable inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes unstable hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes unstable inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini unstable hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini unstable inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop unstable hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop unstable inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
