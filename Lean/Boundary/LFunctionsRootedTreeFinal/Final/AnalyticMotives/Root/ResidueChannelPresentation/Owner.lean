import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Stage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.ResidueLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Channels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Schedules.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Kernels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.SingularSupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Spine.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Certified.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.ResidueChannelPresentation.Payload.Owner

/-!
# Top-root residue-channel presentations

This file aggregates the public root surface for certified residue-channel
presentations: core kernel/support facts, finite spines, certified
presentations, and analytic payload accounting.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Residue-channel aggregate: source presentations retain their source expression. -/
theorem AnalyticMotivesRoot.residueChannelSummary_ofSource_source
    (source : QTraceExpression) :
    (CertifiedResidueChannelPresentation.ofSource source).source =
      source :=
  AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofSource_source
    source

/-- Residue-channel aggregate: component-built presentations retain their residue ledger. -/
theorem AnalyticMotivesRoot.residueChannelSummary_ofComponents_ledger
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
  AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofComponents_ledger
    source
    ledger
    channels
    schedule

/-- Residue-channel aggregate: component-built presentations retain their channel list. -/
theorem AnalyticMotivesRoot.residueChannelSummary_ofComponents_channels
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
  AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofComponents_channels
    source
    ledger
    channels
    schedule

/-- Residue-channel aggregate: component-built ledgers record source, residue ledger, channels, and schedule. -/
theorem AnalyticMotivesRoot.residueChannelSummary_ofComponents_certificateLedger_eq_components
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
  AnalyticMotivesRoot.certifiedResidueChannelPresentation_ofComponents_certificateLedger_eq_components
    source
    ledger
    channels
    schedule

/-- Residue-channel aggregate: imported rectangle count is the imported rectangle-list length. -/
theorem AnalyticMotivesRoot.residueChannelSummary_importedRectangleCount_eq_length
    (presentation : CertifiedResidueChannelPresentation) :
    presentation.importedRectangleCount =
      presentation.importedRectangles.length :=
  AnalyticMotivesRoot.certifiedResidueChannelPresentation_importedRectangleCount_eq_length_importedRectangles
    presentation

/-- Residue-channel aggregate: adding certificates appends imported rectangle payload. -/
theorem AnalyticMotivesRoot.residueChannelSummary_withAdditionalCertificates_importedRectangles
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).importedRectangles =
      presentation.importedRectangles ++
        certificates.importedRectangles :=
  AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_importedRectangles
    presentation
    certificates

/-- Residue-channel aggregate: adding certificates adds rewrite-step payload. -/
theorem AnalyticMotivesRoot.residueChannelSummary_withAdditionalCertificates_rewriteStepCount
    (presentation : CertifiedResidueChannelPresentation)
    (certificates : ResidueChannelCertificateLedger) :
    (presentation.withAdditionalCertificates certificates).rewriteStepCount =
      presentation.rewriteStepCount +
        certificates.rewriteStepCount :=
  AnalyticMotivesRoot.certifiedResidueChannelPresentation_withAdditionalCertificates_rewriteStepCount
    presentation
    certificates

end AnalyticMotives
end LFunctions
end Boundary
