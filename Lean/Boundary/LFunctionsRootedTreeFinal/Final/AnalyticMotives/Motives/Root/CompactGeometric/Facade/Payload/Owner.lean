import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Facade.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Owner

/-!
# Motive-root compact-geometric evaluation payload facade

This file exposes compact-generator evaluation and pullback-evaluation payload
wrappers under the `TraceAnalyticMotive` root facade.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compact-generator evaluation rectangles are extracted from its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangles_eq_certificateLedger
    generator

/-- Compact-generator evaluation imported count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_certificateLedger
    generator

/-- Compact-generator evaluation ledger rectangle count is its rectangle-list length. -/
theorem TraceAnalyticMotive.compactGenerator_evaluation_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.certificateLedger.importedRectangleCount =
      generator.certificateLedger.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.evaluation_certificateLedgerRectangles_length
    generator

/-- Compact-generator evaluation bookkeeping count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationTraceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.evaluationTraceBookkeepingCount_eq_certificateLedger
    generator

/-- Compact-generator evaluation rewrite-step count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_evaluationRewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluationRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.evaluationRewriteStepCount_eq_certificateLedger
    generator

/-- Compact-generator pullback source evaluation rectangles are the target ledger rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism =
      target.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles_eq_target_certificateLedger
    morphism

/-- Compact-generator pullback target evaluation rectangles are the source ledger rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism =
      source.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles_eq_source_certificateLedger
    morphism

/-- Compact-generator pullback source evaluation imported count is counted by the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_target_certificateLedger
    morphism

/-- Compact-generator pullback source evaluation target ledger count is its rectangle-list length. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluation_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluation_certificateLedgerRectangles_length
    morphism

/-- Compact-generator pullback target evaluation imported count is counted by the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_source_certificateLedger
    morphism

/-- Compact-generator pullback target evaluation source ledger count is its rectangle-list length. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluation_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluation_certificateLedgerRectangles_length
    morphism

/-- Compact-generator pullback source evaluation bookkeeping is counted by the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- Compact-generator pullback target evaluation bookkeeping is counted by the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- Compact-generator pullback source evaluation rewrite-step count is counted by the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount_eq_target_certificateLedger
    morphism

/-- Compact-generator pullback target evaluation rewrite-step count is counted by the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationRewriteStepCount_eq_source_certificateLedger
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
