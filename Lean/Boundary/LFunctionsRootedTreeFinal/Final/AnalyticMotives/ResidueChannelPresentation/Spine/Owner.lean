import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.RootFacts.Owner

/-!
# Residue-channel presentation spines

This file owns the raw finite spine of a residue-channel presentation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The raw finite spine of a residue-channel presentation.

The components are source expression, residue ledger, channel expressions, and
schedule.  The certified presentation attaches finite analytic certificate
ledgers to this spine.
-/
abbrev ResidueChannelPresentationSpine :=
  QTraceExpression × ResidueLedger × ResidueChannelExpressionList × TraceSchedule

/-- Build a raw residue-channel presentation spine from its four components. -/
def ResidueChannelPresentationSpine.ofComponents
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    ResidueChannelPresentationSpine :=
  (source, ledger, channels, schedule)

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

/-- A spine built from components has the supplied source expression. -/
theorem ResidueChannelPresentationSpine.ofComponents_source
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    (ResidueChannelPresentationSpine.ofComponents
      source
      ledger
      channels
      schedule).source =
      source :=
  rfl

/-- A spine built from components has the supplied residue ledger. -/
theorem ResidueChannelPresentationSpine.ofComponents_ledger
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    (ResidueChannelPresentationSpine.ofComponents
      source
      ledger
      channels
      schedule).ledger =
      ledger :=
  rfl

/-- A spine built from components has the supplied channel expressions. -/
theorem ResidueChannelPresentationSpine.ofComponents_channels
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    (ResidueChannelPresentationSpine.ofComponents
      source
      ledger
      channels
      schedule).channels =
      channels :=
  rfl

/-- A spine built from components has the supplied trace schedule. -/
theorem ResidueChannelPresentationSpine.ofComponents_schedule
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    (ResidueChannelPresentationSpine.ofComponents
      source
      ledger
      channels
      schedule).schedule =
      schedule :=
  rfl

/--
The canonical component certificate ledger of a residue-channel presentation
spine.

Every certified presentation built from a spine certifies the four finite
components that define the spine itself: source expression, residue ledger,
channel list, and trace schedule.
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

end AnalyticMotives
end LFunctions
end Boundary
