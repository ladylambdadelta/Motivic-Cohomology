import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.LedgerCounts.Owner

/-!
# Motive-root compact pullback evaluation ledger counts

This file exposes certificate-ledger count formulas at compact pullback
evaluation endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source evaluation imported count is counted by the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_target_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_target_certificateLedger
    morphism

/-- Pullback target evaluation imported count is counted by the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_source_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_source_certificateLedger
    morphism

/-- Pullback source evaluation bookkeeping count is counted by the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationTraceBookkeepingCount_eq_target_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- Pullback target evaluation bookkeeping count is counted by the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationTraceBookkeepingCount_eq_source_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- Pullback source evaluation rewrite count is counted by the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationRewriteStepCount_eq_target_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount_eq_target_certificateLedger
    morphism

/-- Pullback target evaluation rewrite count is counted by the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationRewriteStepCount_eq_source_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
        morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount_eq_source_certificateLedger
    morphism

end AnalyticMotives
end LFunctions
end Boundary
