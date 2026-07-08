import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Paths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Coherence.Owner

/-!
# Top-root rewrite certificates

This file collects public certificate-ledger surfaces for analytic trace
rewrites and higher coherence cells under the `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rewrite-certificate aggregate: a Stokes path ledger counts one rewrite step. -/
theorem AnalyticMotivesRoot.rewriteCertificates_stokesPath_rewriteStepCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.stokesPathCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  AnalyticMotivesRoot.stokesPathCertificateLedger_rewriteStepCount
    source
    target

/-- Rewrite-certificate aggregate: a Stokes path ledger has one bookkeeping atom. -/
theorem AnalyticMotivesRoot.rewriteCertificates_stokesPath_traceBookkeepingCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.stokesPathCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  AnalyticMotivesRoot.stokesPathCertificateLedger_traceBookkeepingCount
    source
    target

/-- Rewrite-certificate aggregate: a Fubini path ledger counts one rewrite step. -/
theorem AnalyticMotivesRoot.rewriteCertificates_fubiniPath_rewriteStepCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.fubiniPathCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  AnalyticMotivesRoot.fubiniPathCertificateLedger_rewriteStepCount
    source
    target

/-- Rewrite-certificate aggregate: a Fubini path ledger has one bookkeeping atom. -/
theorem AnalyticMotivesRoot.rewriteCertificates_fubiniPath_traceBookkeepingCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.fubiniPathCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  AnalyticMotivesRoot.fubiniPathCertificateLedger_traceBookkeepingCount
    source
    target

/-- Rewrite-certificate aggregate: Fubini coherence records source path, target path, and cell. -/
theorem AnalyticMotivesRoot.rewriteCertificates_fubiniCoherence_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.fubiniCoherenceCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  AnalyticMotivesRoot.fubiniCoherenceCertificateLedger_traceBookkeepingCount
    source
    target

/-- Rewrite-certificate aggregate: Fubini coherence counts the compared paths. -/
theorem AnalyticMotivesRoot.rewriteCertificates_fubiniCoherence_rewriteStepCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.fubiniCoherenceCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  AnalyticMotivesRoot.fubiniCoherenceCertificateLedger_rewriteStepCount
    source
    target

/-- Rewrite-certificate aggregate: associativity coherence records source path, target path, and cell. -/
theorem AnalyticMotivesRoot.rewriteCertificates_associativityCoherence_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.associativityCoherenceCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  AnalyticMotivesRoot.associativityCoherenceCertificateLedger_traceBookkeepingCount
    source
    target

/-- Rewrite-certificate aggregate: associativity coherence counts the compared paths. -/
theorem AnalyticMotivesRoot.rewriteCertificates_associativityCoherence_rewriteStepCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.associativityCoherenceCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  AnalyticMotivesRoot.associativityCoherenceCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
