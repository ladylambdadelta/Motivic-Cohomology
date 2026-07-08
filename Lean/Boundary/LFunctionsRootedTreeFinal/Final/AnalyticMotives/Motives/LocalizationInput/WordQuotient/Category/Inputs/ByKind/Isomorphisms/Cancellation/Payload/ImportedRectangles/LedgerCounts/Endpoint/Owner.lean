import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.ImportedRectangles.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.LedgerRectangles.Endpoint.Owner

/-!
# Endpoint imported-rectangle ledger facts for named cancellation composites

This file specializes endpoint rectangle-count ledger facts for the six named
localization-input constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
