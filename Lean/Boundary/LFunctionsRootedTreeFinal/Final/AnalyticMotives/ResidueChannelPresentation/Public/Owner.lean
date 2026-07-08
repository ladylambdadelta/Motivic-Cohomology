import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certified.Extension.Owner

/-!
# Residue-channel presentation public facade

This file exposes public root wrappers for certified residue-channel
presentation source constructors and certificate payload laws.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The presentation root exposes empty source presentations. -/
theorem ResidueChannelPresentation.ofSource_source
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).source =
      source :=
  CertifiedResidueChannelPresentation.ofSource_source
    source

/-- The presentation root exposes empty source presentation ledgers. -/
theorem ResidueChannelPresentation.ofSource_ledger
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).ledger =
      ResidueLedger.empty :=
  CertifiedResidueChannelPresentation.ofSource_ledger
    source

/-- The presentation root exposes empty source presentation channels. -/
theorem ResidueChannelPresentation.ofSource_channels
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).channels =
      ResidueChannelExpressionList.empty :=
  CertifiedResidueChannelPresentation.ofSource_channels
    source

/-- The presentation root exposes imported-rectangle count as rectangle-list length. -/
theorem ResidueChannelPresentation.importedRectangleCount_eq_length
    (presentation : CertifiedResidueChannelPresentation) :
    presentation.importedRectangleCount =
      presentation.importedRectangles.length :=
  CertifiedResidueChannelPresentation.importedRectangleCount_eq_length_importedRectangles
    presentation

/-- The presentation root exposes certificate extension of imported-rectangle counts. -/
theorem ResidueChannelPresentation.withAdditionalCertificates_importedRectangleCount
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).importedRectangleCount =
      presentation.importedRectangleCount +
        certificates.importedRectangleCount :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_importedRectangleCount
    presentation
    certificates

end AnalyticMotives
end LFunctions
end Boundary
