import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Trace-calculus payload for input-cancellation composites

This file records the endpoint trace-calculus payload carried by the two
cancellation composites attached to a localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The hom-inverse cancellation composite has the input source ledger as source endpoint. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.sourceCertificateLedger =
      input.localizedSourceObject.certificateLedger :=
  rfl

/-- The hom-inverse cancellation composite has the input source ledger as target endpoint. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_targetCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.targetCertificateLedger =
      input.localizedSourceObject.certificateLedger :=
  rfl

/-- The inverse-hom cancellation composite has the input target ledger as source endpoint. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.sourceCertificateLedger =
      input.localizedTargetObject.certificateLedger :=
  rfl

/-- The inverse-hom cancellation composite has the input target ledger as target endpoint. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_targetCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.targetCertificateLedger =
      input.localizedTargetObject.certificateLedger :=
  rfl

/-- The hom-inverse cancellation composite appends the source endpoint ledger to itself. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_endpointCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        input.localizedSourceObject.certificateLedger
        input.localizedSourceObject.certificateLedger :=
  rfl

/-- The inverse-hom cancellation composite appends the target endpoint ledger to itself. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_endpointCertificateLedger
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        input.localizedTargetObject.certificateLedger
        input.localizedTargetObject.certificateLedger :=
  rfl

/-- Hom-inverse cancellation source bookkeeping is the source object's bookkeeping. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.sourceTraceBookkeepingCount =
      input.localizedSourceObject.traceBookkeepingCount :=
  rfl

/-- Hom-inverse cancellation target bookkeeping is the source object's bookkeeping. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.targetTraceBookkeepingCount =
      input.localizedSourceObject.traceBookkeepingCount :=
  rfl

/-- Inverse-hom cancellation source bookkeeping is the target object's bookkeeping. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.sourceTraceBookkeepingCount =
      input.localizedTargetObject.traceBookkeepingCount :=
  rfl

/-- Inverse-hom cancellation target bookkeeping is the target object's bookkeeping. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.targetTraceBookkeepingCount =
      input.localizedTargetObject.traceBookkeepingCount :=
  rfl

/-- Hom-inverse cancellation endpoint bookkeeping is the doubled source bookkeeping. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.endpointTraceBookkeepingCount =
      input.localizedSourceObject.traceBookkeepingCount +
        input.localizedSourceObject.traceBookkeepingCount :=
  rfl

/-- Inverse-hom cancellation endpoint bookkeeping is the doubled target bookkeeping. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.endpointTraceBookkeepingCount =
      input.localizedTargetObject.traceBookkeepingCount +
        input.localizedTargetObject.traceBookkeepingCount :=
  rfl

/-- Hom-inverse cancellation source rewrite count is the source object's rewrite count. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.sourceRewriteStepCount =
      input.localizedSourceObject.rewriteStepCount :=
  rfl

/-- Hom-inverse cancellation target rewrite count is the source object's rewrite count. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.targetRewriteStepCount =
      input.localizedSourceObject.rewriteStepCount :=
  rfl

/-- Inverse-hom cancellation source rewrite count is the target object's rewrite count. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.sourceRewriteStepCount =
      input.localizedTargetObject.rewriteStepCount :=
  rfl

/-- Inverse-hom cancellation target rewrite count is the target object's rewrite count. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.targetRewriteStepCount =
      input.localizedTargetObject.rewriteStepCount :=
  rfl

/-- Hom-inverse cancellation endpoint rewrite count is the doubled source rewrite count. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_endpointRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.endpointRewriteStepCount =
      input.localizedSourceObject.rewriteStepCount +
        input.localizedSourceObject.rewriteStepCount :=
  rfl

/-- Inverse-hom cancellation endpoint rewrite count is the doubled target rewrite count. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_endpointRewriteStepCount
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.endpointRewriteStepCount =
      input.localizedTargetObject.rewriteStepCount +
        input.localizedTargetObject.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
