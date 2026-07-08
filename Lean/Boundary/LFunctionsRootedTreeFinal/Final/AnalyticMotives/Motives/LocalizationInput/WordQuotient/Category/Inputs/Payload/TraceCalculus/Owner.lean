import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Payload.TraceCalculus.Owner

/-!
# Trace-calculus payload for localized input arrows

This file exposes endpoint certificate ledgers, trace-bookkeeping counts, and
rewrite-step counts for the named forward and inverse arrows attached to a
localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The forward arrow source endpoint ledger is the input source ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.sourceCertificateLedger =
      input.sourceObject.certificateLedger :=
  rfl

/-- The forward arrow target endpoint ledger is the input target ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_targetCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.targetCertificateLedger =
      input.targetObject.certificateLedger :=
  rfl

/-- The inverse arrow source endpoint ledger is the input target ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.sourceCertificateLedger =
      input.targetObject.certificateLedger :=
  rfl

/-- The inverse arrow target endpoint ledger is the input source ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_targetCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.targetCertificateLedger =
      input.sourceObject.certificateLedger :=
  rfl

/-- The forward arrow endpoint ledger is source ledger followed by target ledger. -/
theorem TraceLocalizationInput.localizedForwardArrow_endpointCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        input.sourceObject.certificateLedger
        input.targetObject.certificateLedger :=
  rfl

/-- The inverse arrow endpoint ledger is target ledger followed by source ledger. -/
theorem TraceLocalizationInput.localizedInverseArrow_endpointCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        input.targetObject.certificateLedger
        input.sourceObject.certificateLedger :=
  rfl

/-- The forward arrow source bookkeeping count is the input source bookkeeping count. -/
theorem TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.sourceTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  rfl

/-- The forward arrow target bookkeeping count is the input target bookkeeping count. -/
theorem TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.targetTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  rfl

/-- The inverse arrow source bookkeeping count is the input target bookkeeping count. -/
theorem TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.sourceTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  rfl

/-- The inverse arrow target bookkeeping count is the input source bookkeeping count. -/
theorem TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.targetTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  rfl

/-- The forward arrow endpoint bookkeeping count is source count plus target count. -/
theorem TraceLocalizationInput.localizedForwardArrow_endpointTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.endpointTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount +
        input.targetObject.traceBookkeepingCount :=
  rfl

/-- The inverse arrow endpoint bookkeeping count is target count plus source count. -/
theorem TraceLocalizationInput.localizedInverseArrow_endpointTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.endpointTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount +
        input.sourceObject.traceBookkeepingCount :=
  rfl

/-- The forward arrow source rewrite-step count is the input source rewrite-step count. -/
theorem TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.sourceRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  rfl

/-- The forward arrow target rewrite-step count is the input target rewrite-step count. -/
theorem TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.targetRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  rfl

/-- The inverse arrow source rewrite-step count is the input target rewrite-step count. -/
theorem TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.sourceRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  rfl

/-- The inverse arrow target rewrite-step count is the input source rewrite-step count. -/
theorem TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.targetRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  rfl

/-- The forward arrow endpoint rewrite-step count is source count plus target count. -/
theorem TraceLocalizationInput.localizedForwardArrow_endpointRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow.endpointRewriteStepCount =
      input.sourceObject.rewriteStepCount +
        input.targetObject.rewriteStepCount :=
  rfl

/-- The inverse arrow endpoint rewrite-step count is target count plus source count. -/
theorem TraceLocalizationInput.localizedInverseArrow_endpointRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow.endpointRewriteStepCount =
      input.targetObject.rewriteStepCount +
        input.sourceObject.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
