import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Owner

/-!
# Top-root certified residue-channel presentations

This file exposes constructors and projections for certified residue-channel
presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes certified presentations built from a spine and certificates. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSpineCertificates
    (spine : ResidueChannelPresentationSpine)
    (certificates : ResidueChannelCertificateLedger) :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpineCertificates
    spine
    certificates

/-- The top root exposes certified presentations built from a spine. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSpine
    (spine : ResidueChannelPresentationSpine) :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSpine spine

/-- The top root exposes certified presentations built from raw spine components. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofComponents
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofComponents
    source
    ledger
    channels
    schedule

/-- The top root exposes extension by additional analytic certificates. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates
    presentation
    certificates

/-- The top root exposes certified source presentations. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSource
    (source : QTraceExpression) :
    CertifiedResidueChannelPresentation :=
  CertifiedResidueChannelPresentation.ofSource source

/-- The top root exposes certified presentation sources. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_source
    (presentation : CertifiedResidueChannelPresentation) :
    QTraceExpression :=
  CertifiedResidueChannelPresentation.source presentation

/-- The top root exposes certified presentation residue ledgers. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_ledger
    (presentation : CertifiedResidueChannelPresentation) :
    ResidueLedger :=
  CertifiedResidueChannelPresentation.ledger presentation

/-- The top root exposes certified presentation channels. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_channels
    (presentation : CertifiedResidueChannelPresentation) :
    ResidueChannelExpressionList :=
  CertifiedResidueChannelPresentation.channels presentation

/-- The top root exposes certified presentation schedules. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_schedule
    (presentation : CertifiedResidueChannelPresentation) :
    TraceSchedule :=
  CertifiedResidueChannelPresentation.schedule presentation

/-- The top root exposes certified presentation certificate ledgers. -/
def AnalyticMotivesRoot.certifiedResidueChannelPresentation_certificateLedger
    (presentation : CertifiedResidueChannelPresentation) :
    ResidueChannelCertificateLedger :=
  CertifiedResidueChannelPresentation.certificateLedger presentation

/-- The top root exposes source presentation source projections. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSource_source
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).source =
      source :=
  CertifiedResidueChannelPresentation.ofSource_source
    source

/-- The top root exposes source presentation ledger projections. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSource_ledger
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).ledger =
      ResidueLedger.empty :=
  CertifiedResidueChannelPresentation.ofSource_ledger
    source

/-- The top root exposes source presentation channel projections. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSource_channels
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).channels =
      ResidueChannelExpressionList.empty :=
  CertifiedResidueChannelPresentation.ofSource_channels
    source

/-- The top root exposes source presentation schedule projections. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSource_schedule
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).schedule =
      TraceSchedule.empty :=
  CertifiedResidueChannelPresentation.ofSource_schedule
    source

/-- The top root exposes spine constructor spine projections. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSpine_spine
    (spine : ResidueChannelPresentationSpine) :
    (CertifiedResidueChannelPresentation.ofSpine spine).spine =
      spine :=
  CertifiedResidueChannelPresentation.ofSpine_spine
    spine

/-- The top root exposes spine constructor certificate ledgers. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSpine_certificateLedger
    (spine : ResidueChannelPresentationSpine) :
    (CertifiedResidueChannelPresentation.ofSpine spine).certificateLedger =
      spine.componentCertificateLedger :=
  CertifiedResidueChannelPresentation.ofSpine_certificateLedger
    spine

/-- The top root exposes source projections for component-built presentations. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofComponents_source
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    (CertifiedResidueChannelPresentation.ofComponents
      source
      ledger
      channels
      schedule).source =
      source :=
  CertifiedResidueChannelPresentation.ofComponents_source
    source
    ledger
    channels
    schedule

/-- The top root exposes ledger projections for component-built presentations. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofComponents_ledger
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    (CertifiedResidueChannelPresentation.ofComponents
      source
      ledger
      channels
      schedule).ledger =
      ledger :=
  CertifiedResidueChannelPresentation.ofComponents_ledger
    source
    ledger
    channels
    schedule

/-- The top root exposes channel projections for component-built presentations. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofComponents_channels
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    (CertifiedResidueChannelPresentation.ofComponents
      source
      ledger
      channels
      schedule).channels =
      channels :=
  CertifiedResidueChannelPresentation.ofComponents_channels
    source
    ledger
    channels
    schedule

/-- The top root exposes schedule projections for component-built presentations. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofComponents_schedule
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    (CertifiedResidueChannelPresentation.ofComponents
      source
      ledger
      channels
      schedule).schedule =
      schedule :=
  CertifiedResidueChannelPresentation.ofComponents_schedule
    source
    ledger
    channels
    schedule

/-- The top root exposes certificate ledgers for component-built presentations. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofComponents_certificateLedger
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    (CertifiedResidueChannelPresentation.ofComponents
      source
      ledger
      channels
      schedule).certificateLedger =
      (ResidueChannelPresentationSpine.ofComponents
        source
        ledger
        channels
        schedule).componentCertificateLedger :=
  CertifiedResidueChannelPresentation.ofComponents_certificateLedger
    source
    ledger
    channels
    schedule

/-- The top root exposes the four-component ledger shape for component-built presentations. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofComponents_certificateLedger_eq_components
    (source : QTraceExpression)
    (ledger : ResidueLedger)
    (channels : ResidueChannelExpressionList)
    (schedule : TraceSchedule) :
    (CertifiedResidueChannelPresentation.ofComponents
      source
      ledger
      channels
      schedule).certificateLedger =
      [
        ResidueChannelCertificateAtom.sourceExpression source,
        ResidueChannelCertificateAtom.residueLedger ledger,
        ResidueChannelCertificateAtom.channelList channels,
        ResidueChannelCertificateAtom.traceSchedule schedule
      ] :=
  CertifiedResidueChannelPresentation.ofComponents_certificateLedger_eq_components
    source
    ledger
    channels
    schedule

/-- The top root exposes preservation of spines under certificate extension. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_spine
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).spine =
      presentation.spine :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_spine
    presentation
    certificates

/-- The top root exposes preservation of sources under certificate extension. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_source
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).source =
      presentation.source :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_source
    presentation
    certificates

/-- The top root exposes preservation of residue ledgers under certificate extension. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_ledger
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).ledger =
      presentation.ledger :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_ledger
    presentation
    certificates

/-- The top root exposes preservation of channels under certificate extension. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_channels
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).channels =
      presentation.channels :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_channels
    presentation
    certificates

/-- The top root exposes preservation of schedules under certificate extension. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_schedule
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).schedule =
      presentation.schedule :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_schedule
    presentation
    certificates

/-- The top root exposes appended certificate ledgers under certificate extension. -/
theorem AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_certificateLedger
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).certificateLedger =
      ResidueChannelCertificateLedger.append
        presentation.certificateLedger
        certificates :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_certificateLedger
    presentation
    certificates

end AnalyticMotives
end LFunctions
end Boundary
