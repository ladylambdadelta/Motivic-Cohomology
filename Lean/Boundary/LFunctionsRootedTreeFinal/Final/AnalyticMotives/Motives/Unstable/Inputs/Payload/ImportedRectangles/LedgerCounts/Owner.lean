import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.ImportedRectangles.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.LedgerCounts.Owner

/-!
# Imported-rectangle ledger counts for unstable localization-input arrows

This file exposes source, target, and endpoint imported-rectangle
count-as-ledger-count facts for localization-input forward and inverse arrows
in the unstable analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable forward source imported count is counted by the source endpoint ledger. -/
theorem TraceLocalizationInput.unstableForward_sourceImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangleCount =
      input.unstableForward.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    input

/-- The unstable forward target imported count is counted by the target endpoint ledger. -/
theorem TraceLocalizationInput.unstableForward_targetImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangleCount =
      input.unstableForward.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    input

/-- The unstable inverse source imported count is counted by the source endpoint ledger. -/
theorem TraceLocalizationInput.unstableInverse_sourceImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangleCount =
      input.unstableInverse.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    input

/-- The unstable inverse target imported count is counted by the target endpoint ledger. -/
theorem TraceLocalizationInput.unstableInverse_targetImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangleCount =
      input.unstableInverse.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    input

/-- The unstable forward endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.unstableForward_endpointImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointImportedRectangleCount =
      input.unstableForward.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    input

/-- The unstable inverse endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.unstableInverse_endpointImportedRectangleCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointImportedRectangleCount =
      input.unstableInverse.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    input

end AnalyticMotives
end LFunctions
end Boundary
