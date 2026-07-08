import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Pullback.Payload.Owner

/-!
# Top-root compact pullback evaluation payloads

This file exposes payload endpoint facts for compact-generator pullback on
sections.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source evaluation rectangles agree with the morphism target payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationImportedRectangles_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism =
      morphism.targetImportedRectangles :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangles_eq_morphism_target
    morphism

/-- Pullback target evaluation rectangles agree with the morphism source payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationImportedRectangles_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism =
      morphism.sourceImportedRectangles :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangles_eq_morphism_source
    morphism

/-- Pullback source evaluation imported count agrees with the morphism target count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      morphism.targetImportedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_morphism_target
    morphism

/-- Pullback target evaluation imported count agrees with the morphism source count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      morphism.sourceImportedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_morphism_source
    morphism

/-- Pullback source evaluation bookkeeping count agrees with the morphism target count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationTraceBookkeepingCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        morphism =
      morphism.targetTraceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationTraceBookkeepingCount_eq_morphism_target
    morphism

/-- Pullback target evaluation bookkeeping count agrees with the morphism source count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationTraceBookkeepingCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        morphism =
      morphism.sourceTraceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationTraceBookkeepingCount_eq_morphism_source
    morphism

/-- Pullback source evaluation rewrite count agrees with the morphism target count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationRewriteStepCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        morphism =
      morphism.targetRewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationRewriteStepCount_eq_morphism_target
    morphism

/-- Pullback target evaluation rewrite count agrees with the morphism source count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationRewriteStepCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
        morphism =
      morphism.sourceRewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationRewriteStepCount_eq_morphism_source
    morphism

/-- Pullback source evaluation imported count is counted by its rectangle list. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      (TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism).length :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_length
    morphism

/-- Pullback target evaluation imported count is counted by its rectangle list. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      (TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism).length :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_length
    morphism

end AnalyticMotives
end LFunctions
end Boundary
