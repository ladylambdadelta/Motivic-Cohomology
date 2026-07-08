import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certified.Constructors.Owner

/-!
# Certified presentation certificate extension

This file owns preservation and payload laws for adding analytic certificates
to certified residue-channel presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Adding certificates preserves the underlying spine. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_spine
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).spine =
      presentation.spine :=
  rfl

/-- Adding certificates preserves the source expression. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_source
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).source =
      presentation.source :=
  rfl

/-- Adding certificates preserves the residue ledger. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_ledger
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).ledger =
      presentation.ledger :=
  rfl

/-- Adding certificates preserves the channel expressions. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_channels
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).channels =
      presentation.channels :=
  rfl

/-- Adding certificates preserves the trace schedule. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_schedule
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).schedule =
      presentation.schedule :=
  rfl

/-- Adding certificates appends them to the existing analytic certificate ledger. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_certificateLedger
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).certificateLedger =
      ResidueChannelCertificateLedger.append
        presentation.certificateLedger
        certificates :=
  rfl

/-- Adding certificates adds imported finite-rectangle analytic payload. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_importedRectangleCount
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).importedRectangleCount =
      presentation.importedRectangleCount +
        certificates.importedRectangleCount :=
  ResidueChannelCertificateLedger.append_importedRectangleCount
    presentation.certificateLedger
    certificates

/-- Adding certificates appends imported finite explicit-formula rectangles. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_importedRectangles
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).importedRectangles =
      presentation.importedRectangles ++
        certificates.importedRectangles :=
  ResidueChannelCertificateLedger.append_importedRectangles
    presentation.certificateLedger
    certificates

/-- Imported-rectangle count is the length of the extracted rectangle list. -/
theorem CertifiedResidueChannelPresentation.importedRectangleCount_eq_length_importedRectangles
    (presentation : CertifiedResidueChannelPresentation) :
    presentation.importedRectangleCount =
      presentation.importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    presentation.certificateLedger

/-- Adding certificates adds internal trace-bookkeeping payload. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_traceBookkeepingCount
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).traceBookkeepingCount =
      presentation.traceBookkeepingCount +
        certificates.traceBookkeepingCount :=
  ResidueChannelCertificateLedger.append_traceBookkeepingCount
    presentation.certificateLedger
    certificates

/-- Adding certificates adds explicit rewrite-step payload. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_rewriteStepCount
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).rewriteStepCount =
      presentation.rewriteStepCount +
        certificates.rewriteStepCount :=
  ResidueChannelCertificateLedger.append_rewriteStepCount
    presentation.certificateLedger
    certificates

end AnalyticMotives
end LFunctions
end Boundary
