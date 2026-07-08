import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Owner

/-!
# Top-root certified residue-channel presentation payloads

This file exposes imported-rectangle and trace-calculus payload facts for
certified residue-channel presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes imported rectangle counts for certified presentations. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_importedRectangleCount
    (presentation : CertifiedResidueChannelPresentation) :
    Nat :=
  CertifiedResidueChannelPresentation.importedRectangleCount presentation

/-- The top root exposes imported rectangles for certified presentations. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_importedRectangles
    (presentation : CertifiedResidueChannelPresentation) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  CertifiedResidueChannelPresentation.importedRectangles presentation

/-- The top root exposes trace-bookkeeping counts for certified presentations. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_traceBookkeepingCount
    (presentation : CertifiedResidueChannelPresentation) :
    Nat :=
  CertifiedResidueChannelPresentation.traceBookkeepingCount presentation

/-- The top root exposes rewrite-step counts for certified presentations. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_rewriteStepCount
    (presentation : CertifiedResidueChannelPresentation) :
    Nat :=
  CertifiedResidueChannelPresentation.rewriteStepCount presentation

/-- The top root exposes imported rectangle count as imported rectangle list length. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_importedRectangleCount_eq_length_importedRectangles
    (presentation : CertifiedResidueChannelPresentation) :
    presentation.importedRectangleCount =
      presentation.importedRectangles.length :=
  CertifiedResidueChannelPresentation.importedRectangleCount_eq_length_importedRectangles
    presentation

/-- The top root exposes imported rectangle count extension under certificate extension. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_importedRectangleCount
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).importedRectangleCount =
      presentation.importedRectangleCount +
        certificates.importedRectangleCount :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_importedRectangleCount
    presentation
    certificates

/-- The top root exposes imported rectangle list extension under certificate extension. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_importedRectangles
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).importedRectangles =
      presentation.importedRectangles ++
        certificates.importedRectangles :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_importedRectangles
    presentation
    certificates

/-- The top root exposes trace-bookkeeping extension under certificate extension. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_traceBookkeepingCount
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).traceBookkeepingCount =
      presentation.traceBookkeepingCount +
        certificates.traceBookkeepingCount :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_traceBookkeepingCount
    presentation
    certificates

/-- The top root exposes rewrite-step extension under certificate extension. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_rewriteStepCount
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).rewriteStepCount =
      presentation.rewriteStepCount +
        certificates.rewriteStepCount :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_rewriteStepCount
    presentation
    certificates

/-- The top root exposes source-presentation certificate ledgers. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSource_certificateLedger
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).certificateLedger =
      [
        ResidueChannelCertificateAtom.sourceExpression source,
        ResidueChannelCertificateAtom.residueLedger ResidueLedger.empty,
        ResidueChannelCertificateAtom.channelList ResidueChannelExpressionList.empty,
        ResidueChannelCertificateAtom.traceSchedule TraceSchedule.empty
      ] :=
  CertifiedResidueChannelPresentation.ofSource_certificateLedger
    source

/-- The top root exposes presentation-level imported rectangle count as list length. -/
theorem AnalyticMotivesRoot.residueChannelPresentation_importedRectangleCount_eq_length
    (presentation : CertifiedResidueChannelPresentation) :
    presentation.importedRectangleCount =
      presentation.importedRectangles.length :=
  ResidueChannelPresentation.importedRectangleCount_eq_length
    presentation

/-- The top root exposes presentation-level imported rectangle extension. -/
theorem AnalyticMotivesRoot.residueChannelPresentation_withAdditionalCertificates_importedRectangleCount
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).importedRectangleCount =
      presentation.importedRectangleCount +
        certificates.importedRectangleCount :=
  ResidueChannelPresentation.withAdditionalCertificates_importedRectangleCount
    presentation
    certificates

end AnalyticMotives
end LFunctions
end Boundary
