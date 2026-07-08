import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Spine.Owner

/-!
# Certified residue-channel presentations

This file owns the certified residue-channel presentation type and its basic
constructors and accessors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A certified residue-channel presentation.

The spine is the finite trace-calculus object.  The certificate ledger records
the analytic artifacts that justify using that spine in the trace category:
rectangles, residue ledgers, channel decompositions, schedules, rewrite paths,
and coherence cells.
-/
structure CertifiedResidueChannelPresentation where
  spine : ResidueChannelPresentationSpine
  certificates : ResidueChannelCertificateLedger

/-- Build a certified presentation from a spine and its certificate ledger. -/
def CertifiedResidueChannelPresentation.ofSpineCertificates
    (spine : ResidueChannelPresentationSpine)
    (certificates : ResidueChannelCertificateLedger) :
    CertifiedResidueChannelPresentation where
  spine := spine
  certificates := certificates

/-- Build a certified presentation from a spine using its canonical component certificates. -/
def CertifiedResidueChannelPresentation.ofSpine
    (spine : ResidueChannelPresentationSpine) :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpineCertificates
    spine
    spine.componentCertificateLedger

/-- Build a certified presentation from four raw spine components. -/
def CertifiedResidueChannelPresentation.ofComponents
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpine
    (ResidueChannelPresentationSpine.ofComponents
      source
      ledger
      channels
      schedule)

/-- Add extra analytic certificates to a certified presentation. -/
def CertifiedResidueChannelPresentation.withAdditionalCertificates
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpineCertificates
    presentation.spine
    (ResidueChannelCertificateLedger.append
      presentation.certificates
      certificates)

/-- The source expression of a certified residue-channel presentation. -/
def CertifiedResidueChannelPresentation.source
    (presentation : CertifiedResidueChannelPresentation) :
    QTraceExpression :=
  presentation.spine.source

/-- The residue ledger of a certified residue-channel presentation. -/
def CertifiedResidueChannelPresentation.ledger
    (presentation : CertifiedResidueChannelPresentation) :
    ResidueLedger :=
  presentation.spine.ledger

/-- The channel expressions of a certified residue-channel presentation. -/
def CertifiedResidueChannelPresentation.channels
    (presentation : CertifiedResidueChannelPresentation) :
    ResidueChannelExpressionList :=
  presentation.spine.channels

/-- The schedule of a certified residue-channel presentation. -/
def CertifiedResidueChannelPresentation.schedule
    (presentation : CertifiedResidueChannelPresentation) :
    TraceSchedule :=
  presentation.spine.schedule

/-- The analytic certificate ledger of a certified presentation. -/
def CertifiedResidueChannelPresentation.certificateLedger
    (presentation : CertifiedResidueChannelPresentation) :
    ResidueChannelCertificateLedger :=
  presentation.certificates

/-- The number of imported finite-rectangle analytic artifacts in a certified presentation. -/
def CertifiedResidueChannelPresentation.importedRectangleCount
    (presentation : CertifiedResidueChannelPresentation) :
    Nat :=
  presentation.certificateLedger.importedRectangleCount

/-- The imported finite explicit-formula rectangles in a certified presentation. -/
def CertifiedResidueChannelPresentation.importedRectangles
    (presentation : CertifiedResidueChannelPresentation) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  presentation.certificateLedger.importedRectangles

/-- The number of internal trace-bookkeeping atoms in a certified presentation. -/
def CertifiedResidueChannelPresentation.traceBookkeepingCount
    (presentation : CertifiedResidueChannelPresentation) :
    Nat :=
  presentation.certificateLedger.traceBookkeepingCount

/-- The number of one-step rewrite generators explicitly certified by a presentation. -/
def CertifiedResidueChannelPresentation.rewriteStepCount
    (presentation : CertifiedResidueChannelPresentation) :
    Nat :=
  presentation.certificateLedger.rewriteStepCount

/-- The empty certified presentation on a source expression. -/
def CertifiedResidueChannelPresentation.ofSource
    (source : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpine
    (source,
      ResidueLedger.empty,
      ResidueChannelExpressionList.empty,
      TraceSchedule.empty)

end AnalyticMotives
end LFunctions
end Boundary
