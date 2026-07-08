import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.Owner

/-!
# Imported-rectangle ledger lists in the localized word category

This file records that localized-word object and endpoint imported-rectangle
lists are extracted from their certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Object imported rectangles are extracted from the object certificate ledger. -/
theorem TraceLocalizedWordObject.importedRectangles_eq_certificateLedger_rectangles
    (object : TraceLocalizedWordObject) :
    object.importedRectangles =
      object.certificateLedger.importedRectangles :=
  rfl

/-- Source endpoint imported rectangles are extracted from the source endpoint ledger. -/
theorem TraceLocalizedWordHom.sourceImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.sourceImportedRectangles =
      hom.sourceCertificateLedger.importedRectangles :=
  rfl

/-- Target endpoint imported rectangles are extracted from the target endpoint ledger. -/
theorem TraceLocalizedWordHom.targetImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.targetImportedRectangles =
      hom.targetCertificateLedger.importedRectangles :=
  rfl

/-- Endpoint imported rectangles are extracted from the appended endpoint ledger. -/
theorem TraceLocalizedWordHom.endpointImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.endpointImportedRectangles =
      hom.endpointCertificateLedger.importedRectangles :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_importedRectangles
      hom.sourceCertificateLedger
      hom.targetCertificateLedger)

end AnalyticMotives
end LFunctions
end Boundary
