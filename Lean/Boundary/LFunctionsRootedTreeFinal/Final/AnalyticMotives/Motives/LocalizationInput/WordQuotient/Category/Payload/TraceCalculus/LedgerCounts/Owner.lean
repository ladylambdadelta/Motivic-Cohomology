import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.Owner

/-!
# Trace-calculus ledger-count facts in the localized word category

This file records that localized-word trace-bookkeeping and rewrite-step
payloads are counted by their certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Object bookkeeping payload is counted by its certificate ledger. -/
theorem TraceLocalizedWordObject.traceBookkeepingCount_eq_certificateLedger_count
    (object : TraceLocalizedWordObject) :
    object.traceBookkeepingCount =
      object.certificateLedger.traceBookkeepingCount :=
  rfl

/-- Object rewrite-step payload is counted by its certificate ledger. -/
theorem TraceLocalizedWordObject.rewriteStepCount_eq_certificateLedger_count
    (object : TraceLocalizedWordObject) :
    object.rewriteStepCount =
      object.certificateLedger.rewriteStepCount :=
  rfl

/-- Source endpoint bookkeeping is counted by the source endpoint ledger. -/
theorem TraceLocalizedWordHom.sourceTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.sourceTraceBookkeepingCount =
      hom.sourceCertificateLedger.traceBookkeepingCount :=
  rfl

/-- Target endpoint bookkeeping is counted by the target endpoint ledger. -/
theorem TraceLocalizedWordHom.targetTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.targetTraceBookkeepingCount =
      hom.targetCertificateLedger.traceBookkeepingCount :=
  rfl

/-- Source endpoint rewrite steps are counted by the source endpoint ledger. -/
theorem TraceLocalizedWordHom.sourceRewriteStepCount_eq_certificateLedger_count
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.sourceRewriteStepCount =
      hom.sourceCertificateLedger.rewriteStepCount :=
  rfl

/-- Target endpoint rewrite steps are counted by the target endpoint ledger. -/
theorem TraceLocalizedWordHom.targetRewriteStepCount_eq_certificateLedger_count
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.targetRewriteStepCount =
      hom.targetCertificateLedger.rewriteStepCount :=
  rfl

/-- Endpoint bookkeeping is counted by the appended endpoint ledger. -/
theorem TraceLocalizedWordHom.endpointTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.endpointTraceBookkeepingCount =
      hom.endpointCertificateLedger.traceBookkeepingCount :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      hom.sourceCertificateLedger
      hom.targetCertificateLedger)

/-- Endpoint rewrite steps are counted by the appended endpoint ledger. -/
theorem TraceLocalizedWordHom.endpointRewriteStepCount_eq_certificateLedger_count
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    hom.endpointRewriteStepCount =
      hom.endpointCertificateLedger.rewriteStepCount :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      hom.sourceCertificateLedger
      hom.targetCertificateLedger)

end AnalyticMotives
end LFunctions
end Boundary
