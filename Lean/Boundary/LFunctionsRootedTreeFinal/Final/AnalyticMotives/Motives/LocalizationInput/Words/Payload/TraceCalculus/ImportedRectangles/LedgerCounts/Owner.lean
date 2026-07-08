import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Words.Payload.TraceCalculus.ImportedRectangles.Owner

/-!
# Imported-rectangle ledger-count facts for localization words

This file records that imported-rectangle endpoint counts on localization
words are counted by their endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source endpoint imported-rectangle count is counted by the source certificate ledger. -/
theorem TraceLocalizationWord.sourceImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.sourceImportedRectangleCount =
      word.sourceCertificateLedger.importedRectangleCount :=
  rfl

/-- Target endpoint imported-rectangle count is counted by the target certificate ledger. -/
theorem TraceLocalizationWord.targetImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.targetImportedRectangleCount =
      word.targetCertificateLedger.importedRectangleCount :=
  rfl

/-- Endpoint imported-rectangle count is counted by the appended endpoint certificate ledger. -/
theorem TraceLocalizationWord.endpointImportedRectangleCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.endpointImportedRectangleCount =
      word.endpointCertificateLedger.importedRectangleCount :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      word.sourceCertificateLedger
      word.targetCertificateLedger)

end AnalyticMotives
end LFunctions
end Boundary
