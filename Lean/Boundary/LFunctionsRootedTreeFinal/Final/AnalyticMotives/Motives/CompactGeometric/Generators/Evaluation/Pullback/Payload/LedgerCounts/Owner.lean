import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.LedgerCounts.Owner

/-!
# Ledger counts for compact-generator pullback evaluation payloads

This file records that pullback source and target evaluation endpoint counts
are counted by the certificate ledgers of the corresponding target and source
generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source evaluation imported count is counted by the target ledger. -/
theorem TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      target.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_morphism_target
      morphism)
    (TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_target_certificateLedger
      morphism)

/-- Pullback target evaluation imported count is counted by the source ledger. -/
theorem TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      source.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_morphism_source
      morphism)
    (TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_source_certificateLedger
      morphism)

/-- Pullback source evaluation bookkeeping count is counted by the target ledger. -/
theorem TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        morphism =
      target.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount_eq_morphism_target
      morphism)
    (TraceAnalyticGeometricGenerator.Hom.targetTraceBookkeepingCount_eq_target_certificateLedger
      morphism)

/-- Pullback target evaluation bookkeeping count is counted by the source ledger. -/
theorem TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        morphism =
      source.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount_eq_morphism_source
      morphism)
    (TraceAnalyticGeometricGenerator.Hom.sourceTraceBookkeepingCount_eq_source_certificateLedger
      morphism)

/-- Pullback source evaluation rewrite count is counted by the target ledger. -/
theorem TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        morphism =
      target.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount_eq_morphism_target
      morphism)
    (TraceAnalyticGeometricGenerator.Hom.targetRewriteStepCount_eq_target_certificateLedger
      morphism)

/-- Pullback target evaluation rewrite count is counted by the source ledger. -/
theorem TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
        morphism =
      source.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount_eq_morphism_source
      morphism)
    (TraceAnalyticGeometricGenerator.Hom.sourceRewriteStepCount_eq_source_certificateLedger
      morphism)

end AnalyticMotives
end LFunctions
end Boundary
