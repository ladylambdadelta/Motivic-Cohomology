import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.ImportedRectangles.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.LedgerCounts.Owner

/-!
# Imported-rectangle ledger-count facts for generic inverted inputs

This file records that the hom and inverse arrows of a generic localized-word
isomorphism have imported-rectangle endpoint counts counted by their endpoint
certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The generic hom source count is counted by the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    input

/-- The generic hom target count is counted by the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    input

/-- The generic inverse source count is counted by the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    input

/-- The generic inverse target count is counted by the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    input

/-- The generic hom endpoint count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    input

/-- The generic inverse endpoint count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.localizedWordIso input).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    input

end AnalyticMotives
end LFunctions
end Boundary
