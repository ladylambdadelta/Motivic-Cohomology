import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.ImportedRectangles.LedgerCounts.Owner

/-!
# Imported-rectangle ledger-count facts for localized input arrows

This file records that forward and inverse localized-input arrow
imported-rectangle endpoint counts are counted by endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forward arrow source imported count is counted by the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.sourceImportedRectangleCount =
      input.localizedForwardArrow.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.sourceImportedRectangleCount_eq_certificateLedger_count
    input.localizedForwardArrow

/-- The forward arrow target imported count is counted by the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.targetImportedRectangleCount =
      input.localizedForwardArrow.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.targetImportedRectangleCount_eq_certificateLedger_count
    input.localizedForwardArrow

/-- The inverse arrow source imported count is counted by the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.sourceImportedRectangleCount =
      input.localizedInverseArrow.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.sourceImportedRectangleCount_eq_certificateLedger_count
    input.localizedInverseArrow

/-- The inverse arrow target imported count is counted by the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.targetImportedRectangleCount =
      input.localizedInverseArrow.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.targetImportedRectangleCount_eq_certificateLedger_count
    input.localizedInverseArrow

/-- The forward arrow endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.endpointImportedRectangleCount =
      input.localizedForwardArrow.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.endpointImportedRectangleCount_eq_certificateLedger_count
    input.localizedForwardArrow

/-- The inverse arrow endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.endpointImportedRectangleCount =
      input.localizedInverseArrow.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizedWordHom.endpointImportedRectangleCount_eq_certificateLedger_count
    input.localizedInverseArrow

end AnalyticMotives
end LFunctions
end Boundary
