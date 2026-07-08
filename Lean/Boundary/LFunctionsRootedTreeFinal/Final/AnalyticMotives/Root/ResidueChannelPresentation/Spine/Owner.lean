import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Owner

/-!
# Top-root residue-channel presentation spines

This file exposes the finite spine of a residue-channel presentation and its
canonical component certificate ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes raw spine construction from four finite components. -/
def AnalyticMotivesRoot.residueChannelPresentationSpine_ofComponents
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    ResidueChannelPresentationSpine :=
  ResidueChannelPresentationSpine.ofComponents
    source
    ledger
    channels
    schedule

/-- The top root exposes the source of a residue-channel presentation spine. -/
def AnalyticMotivesRoot.residueChannelPresentationSpine_source
    (presentation : ResidueChannelPresentationSpine) :
    QTraceExpression :=
  ResidueChannelPresentationSpine.source presentation

/-- The top root exposes the residue ledger of a residue-channel presentation spine. -/
def AnalyticMotivesRoot.residueChannelPresentationSpine_ledger
    (presentation : ResidueChannelPresentationSpine) :
    ResidueLedger :=
  ResidueChannelPresentationSpine.ledger presentation

/-- The top root exposes the channel expressions of a residue-channel presentation spine. -/
def AnalyticMotivesRoot.residueChannelPresentationSpine_channels
    (presentation : ResidueChannelPresentationSpine) :
    ResidueChannelExpressionList :=
  ResidueChannelPresentationSpine.channels presentation

/-- The top root exposes the schedule of a residue-channel presentation spine. -/
def AnalyticMotivesRoot.residueChannelPresentationSpine_schedule
    (presentation : ResidueChannelPresentationSpine) :
    TraceSchedule :=
  ResidueChannelPresentationSpine.schedule presentation

/-- The top root exposes the canonical component certificate ledger of a spine. -/
def AnalyticMotivesRoot.residueChannelPresentationSpine_componentCertificateLedger
    (presentation : ResidueChannelPresentationSpine) :
    ResidueChannelCertificateLedger :=
  ResidueChannelPresentationSpine.componentCertificateLedger presentation

/-- The top root exposes the source projection for component-built spines. -/
theorem AnalyticMotivesRoot.residueChannelPresentationSpine_ofComponents_source
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
  ResidueChannelPresentationSpine.ofComponents_source
    source
    ledger
    channels
    schedule

/-- The top root exposes the ledger projection for component-built spines. -/
theorem AnalyticMotivesRoot.residueChannelPresentationSpine_ofComponents_ledger
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
  ResidueChannelPresentationSpine.ofComponents_ledger
    source
    ledger
    channels
    schedule

/-- The top root exposes the channel projection for component-built spines. -/
theorem AnalyticMotivesRoot.residueChannelPresentationSpine_ofComponents_channels
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
  ResidueChannelPresentationSpine.ofComponents_channels
    source
    ledger
    channels
    schedule

/-- The top root exposes the schedule projection for component-built spines. -/
theorem AnalyticMotivesRoot.residueChannelPresentationSpine_ofComponents_schedule
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
  ResidueChannelPresentationSpine.ofComponents_schedule
    source
    ledger
    channels
    schedule

/-- The top root exposes the source-headed component ledger of a spine. -/
theorem AnalyticMotivesRoot.residueChannelPresentationSpine_componentCertificateLedger_source_head
    (presentation : ResidueChannelPresentationSpine) :
    presentation.componentCertificateLedger =
      ResidueChannelCertificateAtom.sourceExpression presentation.source ::
        ResidueChannelCertificateAtom.residueLedger presentation.ledger ::
          ResidueChannelCertificateAtom.channelList presentation.channels ::
            ResidueChannelCertificateAtom.traceSchedule presentation.schedule ::
              ResidueChannelCertificateLedger.empty :=
  ResidueChannelPresentationSpine.componentCertificateLedger_source_head
    presentation

end AnalyticMotives
end LFunctions
end Boundary
