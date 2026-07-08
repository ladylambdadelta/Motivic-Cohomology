import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Words.Payload.TraceCalculus.Owner

/-!
# Imported-rectangle payload for localization words

This file records that imported rectangle lists on localization words are
extracted from their endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source endpoint imported rectangles are extracted from the source certificate ledger. -/
theorem TraceLocalizationWord.sourceImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.sourceImportedRectangles =
      word.sourceCertificateLedger.importedRectangles :=
  rfl

/-- Target endpoint imported rectangles are extracted from the target certificate ledger. -/
theorem TraceLocalizationWord.targetImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.targetImportedRectangles =
      word.targetCertificateLedger.importedRectangles :=
  rfl

/-- Endpoint imported rectangles are extracted from the appended endpoint certificate ledger. -/
theorem TraceLocalizationWord.endpointImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.endpointImportedRectangles =
      word.endpointCertificateLedger.importedRectangles :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_importedRectangles
      word.sourceCertificateLedger
      word.targetCertificateLedger)

end AnalyticMotives
end LFunctions
end Boundary
