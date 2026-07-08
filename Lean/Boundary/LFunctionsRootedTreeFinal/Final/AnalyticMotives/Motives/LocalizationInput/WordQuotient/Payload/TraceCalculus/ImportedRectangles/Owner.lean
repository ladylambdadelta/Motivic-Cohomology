import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.Owner

/-!
# Imported-rectangle payload for localization word classes

This file records that imported rectangle lists on localization word classes
are extracted from their endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source endpoint imported rectangles are extracted from the source certificate ledger. -/
theorem TraceLocalizationWordClass.sourceImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.sourceImportedRectangles =
      wordClass.sourceCertificateLedger.importedRectangles :=
  rfl

/-- Target endpoint imported rectangles are extracted from the target certificate ledger. -/
theorem TraceLocalizationWordClass.targetImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.targetImportedRectangles =
      wordClass.targetCertificateLedger.importedRectangles :=
  rfl

/-- Endpoint imported rectangles are extracted from the appended endpoint certificate ledger. -/
theorem TraceLocalizationWordClass.endpointImportedRectangles_eq_certificateLedger_rectangles
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.endpointImportedRectangles =
      wordClass.endpointCertificateLedger.importedRectangles :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_importedRectangles
      wordClass.sourceCertificateLedger
      wordClass.targetCertificateLedger)

end AnalyticMotives
end LFunctions
end Boundary
