import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.ImportedRectangles.LedgerRectangles.Owner

/-!
# Imported-rectangle ledger-count facts in the localized word category

This file records that imported-rectangle endpoint counts in the localized
word category are counted by the corresponding endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Object imported-rectangle payload is counted by its certificate ledger. -/
theorem TraceLocalizedWordObject.importedRectangleCount_eq_certificateLedger_count
    (object : TraceLocalizedWordObject) :
    object.importedRectangleCount =
      object.certificateLedger.importedRectangleCount :=
  rfl

/-- Source endpoint imported-rectangle count is counted by the source endpoint ledger. -/
theorem TraceLocalizedWordHom.sourceImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.sourceImportedRectangleCount =
      hom.sourceCertificateLedger.importedRectangleCount :=
  rfl

/-- Target endpoint imported-rectangle count is counted by the target endpoint ledger. -/
theorem TraceLocalizedWordHom.targetImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.targetImportedRectangleCount =
      hom.targetCertificateLedger.importedRectangleCount :=
  rfl

/-- Endpoint imported-rectangle count is counted by the appended endpoint ledger. -/
theorem TraceLocalizedWordHom.endpointImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.endpointImportedRectangleCount =
      hom.endpointCertificateLedger.importedRectangleCount :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      hom.sourceCertificateLedger
      hom.targetCertificateLedger)

end AnalyticMotives
end LFunctions
end Boundary
