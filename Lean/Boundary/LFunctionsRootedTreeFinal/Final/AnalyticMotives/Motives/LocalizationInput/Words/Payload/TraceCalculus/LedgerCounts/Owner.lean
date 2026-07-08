import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Words.Payload.TraceCalculus.Owner

/-!
# Trace-calculus ledger-count facts for localization words

This file records that word trace-bookkeeping and rewrite-step payloads are
counted by their endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source endpoint bookkeeping is counted by the source certificate ledger. -/
theorem TraceLocalizationWord.sourceTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.sourceTraceBookkeepingCount =
      word.sourceCertificateLedger.traceBookkeepingCount :=
  rfl

/-- Target endpoint bookkeeping is counted by the target certificate ledger. -/
theorem TraceLocalizationWord.targetTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.targetTraceBookkeepingCount =
      word.targetCertificateLedger.traceBookkeepingCount :=
  rfl

/-- Source endpoint rewrite steps are counted by the source certificate ledger. -/
theorem TraceLocalizationWord.sourceRewriteStepCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.sourceRewriteStepCount =
      word.sourceCertificateLedger.rewriteStepCount :=
  rfl

/-- Target endpoint rewrite steps are counted by the target certificate ledger. -/
theorem TraceLocalizationWord.targetRewriteStepCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.targetRewriteStepCount =
      word.targetCertificateLedger.rewriteStepCount :=
  rfl

/-- Endpoint bookkeeping is counted by the appended endpoint certificate ledger. -/
theorem TraceLocalizationWord.endpointTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.endpointTraceBookkeepingCount =
      word.endpointCertificateLedger.traceBookkeepingCount :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      word.sourceCertificateLedger
      word.targetCertificateLedger)

/-- Endpoint rewrite steps are counted by the appended endpoint certificate ledger. -/
theorem TraceLocalizationWord.endpointRewriteStepCount_eq_certificateLedger_count
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.endpointRewriteStepCount =
      word.endpointCertificateLedger.rewriteStepCount :=
  Eq.symm
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      word.sourceCertificateLedger
      word.targetCertificateLedger)

end AnalyticMotives
end LFunctions
end Boundary
