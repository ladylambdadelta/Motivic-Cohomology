import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Pullback.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Facade.EvaluationPayload.Owner

/-!
# Top-root compact-geometric pullback evaluation payload facade
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes pullback source evaluation rectangle payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism =
      target.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangles_eq_target_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback target evaluation rectangle payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism =
      source.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangles_eq_source_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback source evaluation imported counts. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_target_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback source evaluation target ledger rectangle lengths. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluation_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluation_certificateLedgerRectangles_length
    morphism

/-- The analytic-motives root exposes pullback target evaluation imported counts. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_source_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback target evaluation source ledger rectangle lengths. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluation_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluation_certificateLedgerRectangles_length
    morphism

/-- The analytic-motives root exposes pullback source evaluation bookkeeping counts. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback target evaluation bookkeeping counts. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback source evaluation rewrite-step counts. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationRewriteStepCount_eq_target_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback target evaluation rewrite-step counts. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
        morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationRewriteStepCount_eq_source_certificateLedger
    morphism

end AnalyticMotives
end LFunctions
end Boundary
