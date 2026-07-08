import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.ImportedRectangles.LedgerRectangles.Owner

/-!
# Imported-rectangle ledger extraction in the unstable envelope

This file records that unstable object and hom imported-rectangle lists are
extracted from their certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Object imported rectangles are extracted from the object certificate ledger. -/
theorem TraceUnstableAnalyticMotive.importedRectangles_eq_certificateLedger_rectangles
    (object : TraceUnstableAnalyticMotive) :
    TraceLocalizedWordObject.importedRectangles object =
      (TraceLocalizedWordObject.certificateLedger object).importedRectangles :=
  TraceLocalizedWordObject.importedRectangles_eq_certificateLedger_rectangles
    object

/-- Source endpoint imported rectangles are extracted from the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotiveHom.sourceImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    TraceLocalizedWordHom.sourceImportedRectangles hom =
      (TraceLocalizedWordHom.sourceCertificateLedger hom).importedRectangles :=
  TraceLocalizedWordHom.sourceImportedRectangles_eq_certificateLedger_rectangles
    hom

/-- Target endpoint imported rectangles are extracted from the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotiveHom.targetImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    TraceLocalizedWordHom.targetImportedRectangles hom =
      (TraceLocalizedWordHom.targetCertificateLedger hom).importedRectangles :=
  TraceLocalizedWordHom.targetImportedRectangles_eq_certificateLedger_rectangles
    hom

/-- Endpoint imported rectangles are extracted from the appended endpoint ledger. -/
theorem TraceUnstableAnalyticMotiveHom.endpointImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    TraceLocalizedWordHom.endpointImportedRectangles hom =
      (TraceLocalizedWordHom.endpointCertificateLedger hom).importedRectangles :=
  TraceLocalizedWordHom.endpointImportedRectangles_eq_certificateLedger_rectangles
    hom

end AnalyticMotives
end LFunctions
end Boundary
