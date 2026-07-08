import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.ImportedRectangles.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Owner

/-!
# Ledger-count facts for input-cancellation imported-rectangle payload

This file records that endpoint imported-rectangle counts on the two
cancellation composites attached to a localization input are counted by their
endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Hom-inverse cancellation source rectangle count is counted by its source endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.sourceImportedRectangleCount =
      input.localizedIsoHomInv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.sourceImportedRectangleCount_eq_certificateLedger_count
    input.localizedIsoHomInv

/-- Hom-inverse cancellation target rectangle count is counted by its target endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.targetImportedRectangleCount =
      input.localizedIsoHomInv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.targetImportedRectangleCount_eq_certificateLedger_count
    input.localizedIsoHomInv

/-- Inverse-hom cancellation source rectangle count is counted by its source endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.sourceImportedRectangleCount =
      input.localizedIsoInvHom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.sourceImportedRectangleCount_eq_certificateLedger_count
    input.localizedIsoInvHom

/-- Inverse-hom cancellation target rectangle count is counted by its target endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.targetImportedRectangleCount =
      input.localizedIsoInvHom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.targetImportedRectangleCount_eq_certificateLedger_count
    input.localizedIsoInvHom

/-- Hom-inverse cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.endpointImportedRectangles =
      input.localizedIsoHomInv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizedWordHom.endpointImportedRectangles_eq_certificateLedger_rectangles
    input.localizedIsoHomInv

/-- Inverse-hom cancellation endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.endpointImportedRectangles =
      input.localizedIsoInvHom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizedWordHom.endpointImportedRectangles_eq_certificateLedger_rectangles
    input.localizedIsoInvHom

/-- Hom-inverse cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.endpointImportedRectangleCount =
      input.localizedIsoHomInv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.endpointImportedRectangleCount_eq_certificateLedger_count
    input.localizedIsoHomInv

/-- Inverse-hom cancellation endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.endpointImportedRectangleCount =
      input.localizedIsoInvHom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.endpointImportedRectangleCount_eq_certificateLedger_count
    input.localizedIsoInvHom

end AnalyticMotives
end LFunctions
end Boundary
