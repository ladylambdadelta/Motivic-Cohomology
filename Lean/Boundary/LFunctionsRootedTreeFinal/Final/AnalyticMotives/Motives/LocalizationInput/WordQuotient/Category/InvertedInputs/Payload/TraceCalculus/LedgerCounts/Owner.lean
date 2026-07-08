import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Trace-calculus ledger-count facts for generic inverted inputs

This file records that the hom and inverse arrows of a generic localized-word
isomorphism have trace-bookkeeping and rewrite-step payloads counted by their
endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The generic hom source bookkeeping count is counted by the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.localizedWordIso input).hom.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The generic hom target bookkeeping count is counted by the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.localizedWordIso input).hom.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The generic inverse source bookkeeping count is counted by the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.localizedWordIso input).inv.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The generic inverse target bookkeeping count is counted by the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.localizedWordIso input).inv.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The generic hom source rewrite count is counted by the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.sourceRewriteStepCount =
      (TraceLocalizationInput.localizedWordIso input).hom.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount_eq_certificateLedger_count
    input

/-- The generic hom target rewrite count is counted by the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_targetRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.targetRewriteStepCount =
      (TraceLocalizationInput.localizedWordIso input).hom.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount_eq_certificateLedger_count
    input

/-- The generic inverse source rewrite count is counted by the source endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.sourceRewriteStepCount =
      (TraceLocalizationInput.localizedWordIso input).inv.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount_eq_certificateLedger_count
    input

/-- The generic inverse target rewrite count is counted by the target endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_targetRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.targetRewriteStepCount =
      (TraceLocalizationInput.localizedWordIso input).inv.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount_eq_certificateLedger_count
    input

/-- The generic hom endpoint bookkeeping count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.localizedWordIso input).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The generic inverse endpoint bookkeeping count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.localizedWordIso input).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The generic hom endpoint rewrite count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.endpointRewriteStepCount =
      (TraceLocalizationInput.localizedWordIso input).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    input

/-- The generic inverse endpoint rewrite count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.endpointRewriteStepCount =
      (TraceLocalizationInput.localizedWordIso input).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointRewriteStepCount_eq_certificateLedger_count
    input

end AnalyticMotives
end LFunctions
end Boundary
