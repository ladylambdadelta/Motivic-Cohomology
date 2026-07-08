import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.Owner

/-!
# Trace-calculus ledger-count facts for localization word classes

This file records that word-class trace-bookkeeping and rewrite-step payloads
are counted by their endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source endpoint bookkeeping is counted by the source certificate ledger. -/
theorem TraceLocalizationWordClass.sourceTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.sourceTraceBookkeepingCount =
      wordClass.sourceCertificateLedger.traceBookkeepingCount :=
  rfl

/-- Target endpoint bookkeeping is counted by the target certificate ledger. -/
theorem TraceLocalizationWordClass.targetTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.targetTraceBookkeepingCount =
      wordClass.targetCertificateLedger.traceBookkeepingCount :=
  rfl

/-- Source endpoint rewrite steps are counted by the source certificate ledger. -/
theorem TraceLocalizationWordClass.sourceRewriteStepCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.sourceRewriteStepCount =
      wordClass.sourceCertificateLedger.rewriteStepCount :=
  rfl

/-- Target endpoint rewrite steps are counted by the target certificate ledger. -/
theorem TraceLocalizationWordClass.targetRewriteStepCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.targetRewriteStepCount =
      wordClass.targetCertificateLedger.rewriteStepCount :=
  rfl

/-- Endpoint bookkeeping is counted by the appended endpoint certificate ledger. -/
theorem TraceLocalizationWordClass.endpointTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.endpointTraceBookkeepingCount =
      wordClass.endpointCertificateLedger.traceBookkeepingCount :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      wordClass.sourceCertificateLedger
      wordClass.targetCertificateLedger)

/-- Endpoint rewrite steps are counted by the appended endpoint certificate ledger. -/
theorem TraceLocalizationWordClass.endpointRewriteStepCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.endpointRewriteStepCount =
      wordClass.endpointCertificateLedger.rewriteStepCount :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      wordClass.sourceCertificateLedger
      wordClass.targetCertificateLedger)

end AnalyticMotives
end LFunctions
end Boundary
