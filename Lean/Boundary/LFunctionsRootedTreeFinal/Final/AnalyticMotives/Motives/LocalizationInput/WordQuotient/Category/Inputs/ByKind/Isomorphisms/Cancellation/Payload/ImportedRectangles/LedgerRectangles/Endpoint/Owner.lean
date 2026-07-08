import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.ImportedRectangles.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Owner

/-!
# Endpoint imported-rectangle ledger lists for named cancellation composites

This file specializes endpoint rectangle-list-as-ledger-list facts for the six
named localization-input constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoHomInv.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedIsoHomInv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoInvHom.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedIsoInvHom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoHomInv.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedIsoHomInv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoInvHom.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedIsoInvHom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoHomInv.endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedIsoHomInv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoInvHom.endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedIsoInvHom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoHomInv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedIsoHomInv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoInvHom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedIsoInvHom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoHomInv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedIsoHomInv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoInvHom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedIsoInvHom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoHomInv.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedIsoHomInv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoInvHom.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedIsoInvHom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
