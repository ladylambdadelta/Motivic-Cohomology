import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Trace-calculus ledger-count facts for localized input arrows

This file records that localized forward and inverse input-arrow
trace-bookkeeping and rewrite-step payloads are counted by endpoint certificate
ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forward arrow source bookkeeping is counted by its source endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.sourceTraceBookkeepingCount =
      input.localizedForwardArrow.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.sourceTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedForwardArrow

/-- The forward arrow target bookkeeping is counted by its target endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.targetTraceBookkeepingCount =
      input.localizedForwardArrow.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.targetTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedForwardArrow

/-- The inverse arrow source bookkeeping is counted by its source endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.sourceTraceBookkeepingCount =
      input.localizedInverseArrow.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.sourceTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedInverseArrow

/-- The inverse arrow target bookkeeping is counted by its target endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.targetTraceBookkeepingCount =
      input.localizedInverseArrow.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.targetTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedInverseArrow

/-- The forward arrow source rewrite steps are counted by its source endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.sourceRewriteStepCount =
      input.localizedForwardArrow.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.sourceRewriteStepCount_eq_certificateLedger_count
    input.localizedForwardArrow

/-- The forward arrow target rewrite steps are counted by its target endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.targetRewriteStepCount =
      input.localizedForwardArrow.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.targetRewriteStepCount_eq_certificateLedger_count
    input.localizedForwardArrow

/-- The inverse arrow source rewrite steps are counted by its source endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.sourceRewriteStepCount =
      input.localizedInverseArrow.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.sourceRewriteStepCount_eq_certificateLedger_count
    input.localizedInverseArrow

/-- The inverse arrow target rewrite steps are counted by its target endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.targetRewriteStepCount =
      input.localizedInverseArrow.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.targetRewriteStepCount_eq_certificateLedger_count
    input.localizedInverseArrow

/-- The forward arrow endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.endpointTraceBookkeepingCount =
      input.localizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.endpointTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedForwardArrow

/-- The inverse arrow endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.endpointTraceBookkeepingCount =
      input.localizedInverseArrow.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.endpointTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedInverseArrow

/-- The forward arrow endpoint rewrite steps are counted by its endpoint ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.endpointRewriteStepCount =
      input.localizedForwardArrow.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.endpointRewriteStepCount_eq_certificateLedger_count
    input.localizedForwardArrow

/-- The inverse arrow endpoint rewrite steps are counted by its endpoint ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_endpointRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.endpointRewriteStepCount =
      input.localizedInverseArrow.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.endpointRewriteStepCount_eq_certificateLedger_count
    input.localizedInverseArrow

end AnalyticMotives
end LFunctions
end Boundary
