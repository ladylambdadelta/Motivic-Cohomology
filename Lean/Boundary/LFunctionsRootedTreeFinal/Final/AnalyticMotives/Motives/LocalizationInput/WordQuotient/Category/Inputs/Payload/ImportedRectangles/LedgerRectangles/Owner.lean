import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.ImportedRectangles.LedgerRectangles.Owner

/-!
# Imported-rectangle ledger extraction for localized input arrows

This file records that forward and inverse localized-input arrows extract
their imported rectangle lists from endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forward arrow source imported rectangles are extracted from the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.sourceImportedRectangles =
      input.localizedForwardArrow.sourceCertificateLedger.importedRectangles :=
  TraceLocalizedWordHom.sourceImportedRectangles_eq_certificateLedger_rectangles
    input.localizedForwardArrow

/-- The forward arrow target imported rectangles are extracted from the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.targetImportedRectangles =
      input.localizedForwardArrow.targetCertificateLedger.importedRectangles :=
  TraceLocalizedWordHom.targetImportedRectangles_eq_certificateLedger_rectangles
    input.localizedForwardArrow

/-- The inverse arrow source imported rectangles are extracted from the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.sourceImportedRectangles =
      input.localizedInverseArrow.sourceCertificateLedger.importedRectangles :=
  TraceLocalizedWordHom.sourceImportedRectangles_eq_certificateLedger_rectangles
    input.localizedInverseArrow

/-- The inverse arrow target imported rectangles are extracted from the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.targetImportedRectangles =
      input.localizedInverseArrow.targetCertificateLedger.importedRectangles :=
  TraceLocalizedWordHom.targetImportedRectangles_eq_certificateLedger_rectangles
    input.localizedInverseArrow

/-- The forward arrow endpoint imported rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.endpointImportedRectangles =
      input.localizedForwardArrow.endpointCertificateLedger.importedRectangles :=
  TraceLocalizedWordHom.endpointImportedRectangles_eq_certificateLedger_rectangles
    input.localizedForwardArrow

/-- The inverse arrow endpoint imported rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.endpointImportedRectangles =
      input.localizedInverseArrow.endpointCertificateLedger.importedRectangles :=
  TraceLocalizedWordHom.endpointImportedRectangles_eq_certificateLedger_rectangles
    input.localizedInverseArrow

end AnalyticMotives
end LFunctions
end Boundary
