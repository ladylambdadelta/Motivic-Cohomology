import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Ledger-count identities for unstable localization-input arrows

This file records that unstable forward and inverse input-arrow
trace-bookkeeping and rewrite-step payloads are counted by their endpoint
certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable forward source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.unstableForward_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceTraceBookkeepingCount =
      input.unstableForward.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable forward target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.unstableForward_targetTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableForward.targetTraceBookkeepingCount =
      input.unstableForward.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.unstableInverse_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceTraceBookkeepingCount =
      input.unstableInverse.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.unstableInverse_targetTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetTraceBookkeepingCount =
      input.unstableInverse.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable forward source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.unstableForward_sourceRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableForward.sourceRewriteStepCount =
      input.unstableForward.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    input

/-- The unstable forward target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.unstableForward_targetRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableForward.targetRewriteStepCount =
      input.unstableForward.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    input

/-- The unstable inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.unstableInverse_sourceRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableInverse.sourceRewriteStepCount =
      input.unstableInverse.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    input

/-- The unstable inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.unstableInverse_targetRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableInverse.targetRewriteStepCount =
      input.unstableInverse.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    input

/-- The unstable forward endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.unstableForward_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointTraceBookkeepingCount =
      input.unstableForward.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.unstableInverse_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointTraceBookkeepingCount =
      input.unstableInverse.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable forward endpoint rewrite steps are counted by its endpoint ledger. -/
theorem TraceLocalizationInput.unstableForward_endpointRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableForward.endpointRewriteStepCount =
      input.unstableForward.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    input

/-- The unstable inverse endpoint rewrite steps are counted by its endpoint ledger. -/
theorem TraceLocalizationInput.unstableInverse_endpointRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableInverse.endpointRewriteStepCount =
      input.unstableInverse.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointRewriteStepCount_eq_certificateLedger_count
    input

end AnalyticMotives
end LFunctions
end Boundary
