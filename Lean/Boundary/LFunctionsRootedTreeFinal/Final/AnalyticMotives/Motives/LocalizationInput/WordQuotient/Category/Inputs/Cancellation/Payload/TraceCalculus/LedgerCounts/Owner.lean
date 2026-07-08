import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Owner

/-!
# Ledger-count facts for input-cancellation composites

This file records that endpoint trace-calculus counts on the two cancellation
composites attached to a localization input are counted by their endpoint
certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Hom-inverse cancellation source bookkeeping is counted by its source endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.sourceTraceBookkeepingCount =
      input.localizedIsoHomInv.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordHom.sourceTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedIsoHomInv

/-- Hom-inverse cancellation target bookkeeping is counted by its target endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.targetTraceBookkeepingCount =
      input.localizedIsoHomInv.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordHom.targetTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedIsoHomInv

/-- Inverse-hom cancellation source bookkeeping is counted by its source endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.sourceTraceBookkeepingCount =
      input.localizedIsoInvHom.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordHom.sourceTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedIsoInvHom

/-- Inverse-hom cancellation target bookkeeping is counted by its target endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.targetTraceBookkeepingCount =
      input.localizedIsoInvHom.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordHom.targetTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedIsoInvHom

/-- Hom-inverse cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.endpointTraceBookkeepingCount =
      input.localizedIsoHomInv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordHom.endpointTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedIsoHomInv

/-- Inverse-hom cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.endpointTraceBookkeepingCount =
      input.localizedIsoInvHom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordHom.endpointTraceBookkeepingCount_eq_certificateLedger_count
    input.localizedIsoInvHom

/-- Hom-inverse cancellation source rewrite count is counted by its source endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.sourceRewriteStepCount =
      input.localizedIsoHomInv.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizedWordHom.sourceRewriteStepCount_eq_certificateLedger_count
    input.localizedIsoHomInv

/-- Hom-inverse cancellation target rewrite count is counted by its target endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.targetRewriteStepCount =
      input.localizedIsoHomInv.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizedWordHom.targetRewriteStepCount_eq_certificateLedger_count
    input.localizedIsoHomInv

/-- Inverse-hom cancellation source rewrite count is counted by its source endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.sourceRewriteStepCount =
      input.localizedIsoInvHom.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizedWordHom.sourceRewriteStepCount_eq_certificateLedger_count
    input.localizedIsoInvHom

/-- Inverse-hom cancellation target rewrite count is counted by its target endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.targetRewriteStepCount =
      input.localizedIsoInvHom.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizedWordHom.targetRewriteStepCount_eq_certificateLedger_count
    input.localizedIsoInvHom

/-- Hom-inverse cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoHomInv.endpointRewriteStepCount =
      input.localizedIsoHomInv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizedWordHom.endpointRewriteStepCount_eq_certificateLedger_count
    input.localizedIsoHomInv

/-- Inverse-hom cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.localizedIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.localizedIsoInvHom.endpointRewriteStepCount =
      input.localizedIsoInvHom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizedWordHom.endpointRewriteStepCount_eq_certificateLedger_count
    input.localizedIsoInvHom

end AnalyticMotives
end LFunctions
end Boundary
