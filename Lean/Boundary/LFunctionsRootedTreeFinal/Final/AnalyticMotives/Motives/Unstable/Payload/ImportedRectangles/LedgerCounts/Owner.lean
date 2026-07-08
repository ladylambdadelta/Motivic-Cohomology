import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Payload.ImportedRectangles.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.ImportedRectangles.LedgerCounts.Owner

/-!
# Imported-rectangle ledger counts in the unstable envelope

This file records that unstable object and hom imported-rectangle counts are
counted by their certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Object imported-rectangle payload is counted by its certificate ledger. -/
theorem TraceUnstableAnalyticMotive.importedRectangleCount_eq_certificateLedger_count
    (object : TraceUnstableAnalyticMotive) :
    TraceLocalizedWordObject.importedRectangleCount object =
      (TraceLocalizedWordObject.certificateLedger object).importedRectangleCount :=
  TraceLocalizedWordObject.importedRectangleCount_eq_certificateLedger_count
    object

/-- Source endpoint imported-rectangle count is counted by the source ledger. -/
theorem TraceUnstableAnalyticMotiveHom.sourceImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    TraceLocalizedWordHom.sourceImportedRectangleCount hom =
      (TraceLocalizedWordHom.sourceCertificateLedger hom).importedRectangleCount :=
  TraceLocalizedWordHom.sourceImportedRectangleCount_eq_certificateLedger_count
    hom

/-- Target endpoint imported-rectangle count is counted by the target ledger. -/
theorem TraceUnstableAnalyticMotiveHom.targetImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    TraceLocalizedWordHom.targetImportedRectangleCount hom =
      (TraceLocalizedWordHom.targetCertificateLedger hom).importedRectangleCount :=
  TraceLocalizedWordHom.targetImportedRectangleCount_eq_certificateLedger_count
    hom

/-- Endpoint imported-rectangle count is counted by the appended endpoint ledger. -/
theorem TraceUnstableAnalyticMotiveHom.endpointImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    TraceLocalizedWordHom.endpointImportedRectangleCount hom =
      (TraceLocalizedWordHom.endpointCertificateLedger hom).importedRectangleCount :=
  TraceLocalizedWordHom.endpointImportedRectangleCount_eq_certificateLedger_count
    hom

end AnalyticMotives
end LFunctions
end Boundary
