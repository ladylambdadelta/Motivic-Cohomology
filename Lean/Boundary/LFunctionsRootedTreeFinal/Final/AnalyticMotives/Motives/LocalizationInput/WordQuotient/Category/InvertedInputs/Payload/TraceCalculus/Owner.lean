import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.TraceCalculus.Owner

/-!
# Generic inverted-input trace-calculus payload

This file exposes certificate-ledger, trace-bookkeeping, and rewrite-step
payload carried by the hom and inverse arrows of the generic localized-word
isomorphism attached to a concrete localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The generic localized-input isomorphism hom source ledger is the input source ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.sourceCertificateLedger =
      input.sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedForwardArrow_sourceCertificateLedger
    input

/-- The generic localized-input isomorphism hom target ledger is the input target ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_targetCertificateLedger
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.targetCertificateLedger =
      input.targetObject.certificateLedger :=
  TraceLocalizationInput.localizedForwardArrow_targetCertificateLedger
    input

/-- The generic localized-input isomorphism inverse source ledger is the input target ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.sourceCertificateLedger =
      input.targetObject.certificateLedger :=
  TraceLocalizationInput.localizedInverseArrow_sourceCertificateLedger
    input

/-- The generic localized-input isomorphism inverse target ledger is the input source ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_targetCertificateLedger
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.targetCertificateLedger =
      input.sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedInverseArrow_targetCertificateLedger
    input

/-- The generic localized-input isomorphism hom endpoint ledger is source ledger then target ledger. -/
theorem TraceLocalizationInput.localizedWordIso_hom_endpointCertificateLedger
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.endpointCertificateLedger =
      input.sourceObject.certificateLedger ++
        input.targetObject.certificateLedger :=
  TraceLocalizationInput.localizedForwardArrow_endpointCertificateLedger
    input

/-- The generic localized-input isomorphism inverse endpoint ledger is target ledger then source ledger. -/
theorem TraceLocalizationInput.localizedWordIso_inv_endpointCertificateLedger
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.endpointCertificateLedger =
      input.targetObject.certificateLedger ++
        input.sourceObject.certificateLedger :=
  TraceLocalizationInput.localizedInverseArrow_endpointCertificateLedger
    input

/-- The generic localized-input isomorphism hom source bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.localizedWordIso_hom_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.sourceTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount
    input

/-- The generic localized-input isomorphism hom target bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.localizedWordIso_hom_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.targetTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount
    input

/-- The generic localized-input isomorphism inverse source bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.localizedWordIso_inv_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.sourceTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceTraceBookkeepingCount
    input

/-- The generic localized-input isomorphism inverse target bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.localizedWordIso_inv_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.targetTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_targetTraceBookkeepingCount
    input

/-- The generic hom endpoint bookkeeping count is source count plus target count. -/
theorem TraceLocalizationInput.localizedWordIso_hom_endpointTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.endpointTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount +
        input.targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointTraceBookkeepingCount
    input

/-- The generic inverse endpoint bookkeeping count is target count plus source count. -/
theorem TraceLocalizationInput.localizedWordIso_inv_endpointTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.endpointTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount +
        input.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointTraceBookkeepingCount
    input

/-- The generic localized-input isomorphism hom source rewrite count is the input source count. -/
theorem TraceLocalizationInput.localizedWordIso_hom_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.sourceRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount
    input

/-- The generic localized-input isomorphism hom target rewrite count is the input target count. -/
theorem TraceLocalizationInput.localizedWordIso_hom_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.targetRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount
    input

/-- The generic localized-input isomorphism inverse source rewrite count is the input target count. -/
theorem TraceLocalizationInput.localizedWordIso_inv_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.sourceRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceRewriteStepCount
    input

/-- The generic localized-input isomorphism inverse target rewrite count is the input source count. -/
theorem TraceLocalizationInput.localizedWordIso_inv_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.targetRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_targetRewriteStepCount
    input

/-- The generic hom endpoint rewrite count is source count plus target count. -/
theorem TraceLocalizationInput.localizedWordIso_hom_endpointRewriteStepCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom.endpointRewriteStepCount =
      input.sourceObject.rewriteStepCount +
        input.targetObject.rewriteStepCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointRewriteStepCount
    input

/-- The generic inverse endpoint rewrite count is target count plus source count. -/
theorem TraceLocalizationInput.localizedWordIso_inv_endpointRewriteStepCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv.endpointRewriteStepCount =
      input.targetObject.rewriteStepCount +
        input.sourceObject.rewriteStepCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointRewriteStepCount
    input

end AnalyticMotives
end LFunctions
end Boundary
