import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.ImportedRectangles.Owner

/-!
# Imported-rectangle ledger-count facts for localization word classes

This file records that imported-rectangle endpoint counts on localization word
classes are counted by their endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source endpoint imported-rectangle count is counted by the source certificate ledger. -/
theorem TraceLocalizationWordClass.sourceImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.sourceImportedRectangleCount =
      wordClass.sourceCertificateLedger.importedRectangleCount :=
  rfl

/-- Target endpoint imported-rectangle count is counted by the target certificate ledger. -/
theorem TraceLocalizationWordClass.targetImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.targetImportedRectangleCount =
      wordClass.targetCertificateLedger.importedRectangleCount :=
  rfl

/-- Endpoint imported-rectangle count is counted by the appended endpoint certificate ledger. -/
theorem TraceLocalizationWordClass.endpointImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.endpointImportedRectangleCount =
      wordClass.endpointCertificateLedger.importedRectangleCount :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      wordClass.sourceCertificateLedger
      wordClass.targetCertificateLedger)

end AnalyticMotives
end LFunctions
end Boundary
