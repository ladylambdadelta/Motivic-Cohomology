import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Pullback.Payload.LedgerCounts.Owner

/-!
# Top-root compact pullback evaluation ledger counts

This file exposes certificate-ledger count formulas at compact pullback
evaluation endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source evaluation imported count is counted by the target ledger. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_target_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_target_certificateLedger_root
    morphism

/-- Pullback target evaluation imported count is counted by the source ledger. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_source_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_source_certificateLedger_root
    morphism

/-- Pullback source evaluation bookkeeping count is counted by the target ledger. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationTraceBookkeepingCount_eq_target_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationTraceBookkeepingCount_eq_target_certificateLedger_root
    morphism

/-- Pullback target evaluation bookkeeping count is counted by the source ledger. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationTraceBookkeepingCount_eq_source_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationTraceBookkeepingCount_eq_source_certificateLedger_root
    morphism

/-- Pullback source evaluation rewrite count is counted by the target ledger. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationRewriteStepCount_eq_target_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationRewriteStepCount_eq_target_certificateLedger_root
    morphism

/-- Pullback target evaluation rewrite count is counted by the source ledger. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationRewriteStepCount_eq_source_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
        morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationRewriteStepCount_eq_source_certificateLedger_root
    morphism

end AnalyticMotives
end LFunctions
end Boundary
