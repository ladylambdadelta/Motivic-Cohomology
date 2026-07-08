import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.ImportedRectangles.Isomorphisms.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.ImportedRectangles.LedgerCounts.Owner

/-!
# Imported-rectangle ledger counts for unstable localization-input isomorphisms

This file exposes imported-rectangle count-as-ledger-count facts for the hom
and inverse of each localization-input isomorphism after passage to the
unstable analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable isomorphism hom source imported count is counted by the source ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.sourceImportedRectangleCount =
      input.unstableIso.hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism hom target imported count is counted by the target ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.targetImportedRectangleCount =
      input.unstableIso.hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism inverse source imported count is counted by the source ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.sourceImportedRectangleCount =
      input.unstableIso.inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism inverse target imported count is counted by the target ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.targetImportedRectangleCount =
      input.unstableIso.inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism hom endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.endpointImportedRectangleCount =
      input.unstableIso.hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism inverse endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.endpointImportedRectangleCount =
      input.unstableIso.inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    input

end AnalyticMotives
end LFunctions
end Boundary
