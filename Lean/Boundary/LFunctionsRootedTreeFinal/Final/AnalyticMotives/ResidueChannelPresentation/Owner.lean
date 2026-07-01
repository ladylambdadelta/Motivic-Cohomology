import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Stage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Kernels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.SingularSupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.ResidueLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Channels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Schedules.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.AnalyticPayload.Owner

/-!
# Residue-channel presentations

This directory owns the concrete analytic presentations whose traces generate
the analytic motive category.

A presentation is intended to package kernels, singular support, contour and
residue bookkeeping, channels, schedules, and analytic certificates.  It is the
main object-level input to the later trace-correspondence category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The raw finite spine of a residue-channel presentation.

The components are source expression, residue ledger, channel expressions, and
schedule.  The certified presentation below attaches finite analytic
certificate ledgers to this spine.
-/
abbrev ResidueChannelPresentationSpine :=
  QTraceExpression × ResidueLedger × ResidueChannelExpressionList × TraceSchedule

/-- The source expression of a raw residue-channel presentation spine. -/
def ResidueChannelPresentationSpine.source
    (presentation : ResidueChannelPresentationSpine) : QTraceExpression :=
  presentation.1

/-- The residue ledger of a raw residue-channel presentation spine. -/
def ResidueChannelPresentationSpine.ledger
    (presentation : ResidueChannelPresentationSpine) : ResidueLedger :=
  presentation.2.1

/-- The channel expressions of a raw residue-channel presentation spine. -/
def ResidueChannelPresentationSpine.channels
    (presentation : ResidueChannelPresentationSpine) :
    ResidueChannelExpressionList :=
  presentation.2.2.1

/-- The schedule of a raw residue-channel presentation spine. -/
def ResidueChannelPresentationSpine.schedule
    (presentation : ResidueChannelPresentationSpine) : TraceSchedule :=
  presentation.2.2.2

/--
The canonical component certificate ledger of a residue-channel presentation
spine.

Every certified presentation built from a spine should at least certify the
four finite components that define the spine itself: source expression, residue
ledger, channel list, and trace schedule.
-/
def ResidueChannelPresentationSpine.componentCertificateLedger
    (presentation : ResidueChannelPresentationSpine) :
    ResidueChannelCertificateLedger :=
  [
    ResidueChannelCertificateAtom.sourceExpression presentation.source,
    ResidueChannelCertificateAtom.residueLedger presentation.ledger,
    ResidueChannelCertificateAtom.channelList presentation.channels,
    ResidueChannelCertificateAtom.traceSchedule presentation.schedule
  ]

/-- The component certificate ledger of a spine starts with its source expression. -/
theorem ResidueChannelPresentationSpine.componentCertificateLedger_source_head
    (presentation : ResidueChannelPresentationSpine) :
    presentation.componentCertificateLedger =
      ResidueChannelCertificateAtom.sourceExpression presentation.source ::
        ResidueChannelCertificateAtom.residueLedger presentation.ledger ::
          ResidueChannelCertificateAtom.channelList presentation.channels ::
            ResidueChannelCertificateAtom.traceSchedule presentation.schedule ::
              ResidueChannelCertificateLedger.empty :=
  rfl

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

/-- The number of internal trace-bookkeeping atoms in a certified presentation. -/
def CertifiedResidueChannelPresentation.traceBookkeepingCount
    (presentation : CertifiedResidueChannelPresentation) :
    Nat :=
  presentation.certificateLedger.traceBookkeepingCount

/-- The empty certified presentation on a source expression. -/
def CertifiedResidueChannelPresentation.ofSource
    (source : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpine
    (source,
      ResidueLedger.empty,
      ResidueChannelExpressionList.empty,
      TraceSchedule.empty)

/-- A certified presentation built from a source has that source. -/
theorem CertifiedResidueChannelPresentation.ofSource_source
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).source =
      source :=
  rfl

/-- A certified presentation built from a source has an empty residue ledger. -/
theorem CertifiedResidueChannelPresentation.ofSource_ledger
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).ledger =
      ResidueLedger.empty :=
  rfl

/-- A certified presentation built from a source has no output channels. -/
theorem CertifiedResidueChannelPresentation.ofSource_channels
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).channels =
      ResidueChannelExpressionList.empty :=
  rfl

/-- A certified presentation built from a source has the empty schedule. -/
theorem CertifiedResidueChannelPresentation.ofSource_schedule
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).schedule =
      TraceSchedule.empty :=
  rfl

/-- A certified presentation built from a spine has that spine. -/
theorem CertifiedResidueChannelPresentation.ofSpine_spine
    (spine : ResidueChannelPresentationSpine) :
    (CertifiedResidueChannelPresentation.ofSpine spine).spine =
      spine :=
  rfl

/-- A certified presentation built from a spine has the spine's canonical certificates. -/
theorem CertifiedResidueChannelPresentation.ofSpine_certificateLedger
    (spine : ResidueChannelPresentationSpine) :
    (CertifiedResidueChannelPresentation.ofSpine spine).certificateLedger =
      spine.componentCertificateLedger :=
  rfl

/-- Adding certificates preserves the underlying spine. -/
theorem CertifiedResidueChannelPresentation.withAdditionalCertificates_spine
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).spine =
      presentation.spine :=
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

/-- A certified presentation built from a source carries the canonical component ledger. -/
theorem CertifiedResidueChannelPresentation.ofSource_certificateLedger
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).certificateLedger =
      [
        ResidueChannelCertificateAtom.sourceExpression source,
        ResidueChannelCertificateAtom.residueLedger ResidueLedger.empty,
        ResidueChannelCertificateAtom.channelList ResidueChannelExpressionList.empty,
        ResidueChannelCertificateAtom.traceSchedule TraceSchedule.empty
      ] :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
