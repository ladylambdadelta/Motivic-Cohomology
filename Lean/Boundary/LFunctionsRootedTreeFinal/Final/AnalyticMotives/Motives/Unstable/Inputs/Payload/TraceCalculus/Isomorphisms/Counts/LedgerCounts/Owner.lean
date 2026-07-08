import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Ledger-count identities for unstable localization-input isomorphisms

This file records that the hom and inverse of each unstable localization-input
isomorphism have trace-bookkeeping and rewrite-step payloads counted by their
endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable isomorphism hom source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.sourceTraceBookkeepingCount =
      input.unstableIso.hom.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism hom target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.targetTraceBookkeepingCount =
      input.unstableIso.hom.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism inverse source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.sourceTraceBookkeepingCount =
      input.unstableIso.inv.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism inverse target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.targetTraceBookkeepingCount =
      input.unstableIso.inv.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism hom source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.sourceRewriteStepCount =
      input.unstableIso.hom.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_sourceRewriteStepCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism hom target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_targetRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.targetRewriteStepCount =
      input.unstableIso.hom.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_targetRewriteStepCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism inverse source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.sourceRewriteStepCount =
      input.unstableIso.inv.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_sourceRewriteStepCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism inverse target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_targetRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.targetRewriteStepCount =
      input.unstableIso.inv.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_targetRewriteStepCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.endpointTraceBookkeepingCount =
      input.unstableIso.hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.endpointTraceBookkeepingCount =
      input.unstableIso.inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism hom endpoint rewrite steps are counted by its endpoint ledger. -/
theorem TraceLocalizationInput.unstableIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.hom.endpointRewriteStepCount =
      input.unstableIso.hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    input

/-- The unstable isomorphism inverse endpoint rewrite steps are counted by its endpoint ledger. -/
theorem TraceLocalizationInput.unstableIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (input : TraceLocalizationInput) :
    input.unstableIso.inv.endpointRewriteStepCount =
      input.unstableIso.inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    input

end AnalyticMotives
end LFunctions
end Boundary
