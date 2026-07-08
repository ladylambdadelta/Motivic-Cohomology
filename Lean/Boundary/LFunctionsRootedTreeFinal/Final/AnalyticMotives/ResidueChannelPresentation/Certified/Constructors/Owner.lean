import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certified.Owner

/-!
# Certified presentation constructor laws

This file owns projection laws for canonical certified residue-channel
presentation constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

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

/-- A certified presentation built from components has the supplied source. -/
theorem CertifiedResidueChannelPresentation.ofComponents_source
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
  rfl

/-- A certified presentation built from components has the supplied ledger. -/
theorem CertifiedResidueChannelPresentation.ofComponents_ledger
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
  rfl

/-- A certified presentation built from components has the supplied channels. -/
theorem CertifiedResidueChannelPresentation.ofComponents_channels
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
  rfl

/-- A certified presentation built from components has the supplied schedule. -/
theorem CertifiedResidueChannelPresentation.ofComponents_schedule
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
  rfl

/-- A certified presentation built from components uses their canonical component ledger. -/
theorem CertifiedResidueChannelPresentation.ofComponents_certificateLedger
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
  rfl

/-- A certified presentation built from components certifies the four supplied components. -/
theorem CertifiedResidueChannelPresentation.ofComponents_certificateLedger_eq_components
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
  rfl

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
