import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.ImportedRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.LedgerRectangles.Owner

/-!
# Imported-rectangle ledger extraction for unstable localization-input arrows

This file exposes source, target, and endpoint imported-rectangle
list-as-ledger-list facts for localization-input forward and inverse arrows in
the unstable analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable forward source rectangles are extracted from the source endpoint ledger. -/
theorem TraceLocalizationInput.unstableForward_sourceImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceImportedRectangles =
      input.unstableForward.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The unstable forward target rectangles are extracted from the target endpoint ledger. -/
theorem TraceLocalizationInput.unstableForward_targetImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableForward.targetImportedRectangles =
      input.unstableForward.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The unstable inverse source rectangles are extracted from the source endpoint ledger. -/
theorem TraceLocalizationInput.unstableInverse_sourceImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceImportedRectangles =
      input.unstableInverse.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The unstable inverse target rectangles are extracted from the target endpoint ledger. -/
theorem TraceLocalizationInput.unstableInverse_targetImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetImportedRectangles =
      input.unstableInverse.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The unstable forward endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.unstableForward_endpointImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointImportedRectangles =
      input.unstableForward.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The unstable inverse endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.unstableInverse_endpointImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointImportedRectangles =
      input.unstableInverse.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    input

end AnalyticMotives
end LFunctions
end Boundary
