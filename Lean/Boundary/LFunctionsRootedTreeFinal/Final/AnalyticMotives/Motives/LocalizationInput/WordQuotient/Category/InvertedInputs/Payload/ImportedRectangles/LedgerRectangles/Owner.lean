import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.LedgerRectangles.Owner

/-!
# Imported-rectangle ledger extraction for generic inverted inputs

This file records that the hom and inverse arrows of a generic localized-word
isomorphism extract imported rectangle lists from their endpoint certificate
ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The generic hom source rectangles are extracted from the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.sourceImportedRectangles =
      (TraceLocalizationInput.localizedWordIso input).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The generic hom target rectangles are extracted from the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.targetImportedRectangles =
      (TraceLocalizationInput.localizedWordIso input).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The generic inverse source rectangles are extracted from the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.sourceImportedRectangles =
      (TraceLocalizationInput.localizedWordIso input).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The generic inverse target rectangles are extracted from the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.targetImportedRectangles =
      (TraceLocalizationInput.localizedWordIso input).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The generic hom endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.endpointImportedRectangles =
      (TraceLocalizationInput.localizedWordIso input).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    input

/-- The generic inverse endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.endpointImportedRectangles =
      (TraceLocalizationInput.localizedWordIso input).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    input

end AnalyticMotives
end LFunctions
end Boundary
