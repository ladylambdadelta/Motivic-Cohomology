import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.ImportedRectangles.Isomorphisms.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.ImportedRectangles.LedgerRectangles.Owner

/-!
# Imported-rectangle ledger extraction for unstable localization-input isomorphisms

This file exposes imported-rectangle list-as-ledger-list facts for the hom and
inverse of each localization-input isomorphism after passage to the unstable
analytic-motive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable isomorphism hom source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.sourceImportedRectangles =
      input.unstableIso.hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The unstable isomorphism hom target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.targetImportedRectangles =
      input.unstableIso.hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The unstable isomorphism inverse source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.sourceImportedRectangles =
      input.unstableIso.inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The unstable isomorphism inverse target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.targetImportedRectangles =
      input.unstableIso.inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The unstable isomorphism hom endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.endpointImportedRectangles =
      input.unstableIso.hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The unstable isomorphism inverse endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.endpointImportedRectangles =
      input.unstableIso.inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedWordIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    input

end AnalyticMotives
end LFunctions
end Boundary
