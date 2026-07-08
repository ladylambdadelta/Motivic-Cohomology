import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.Owner

/-!
# Motive-root compact pullback evaluation payloads

This file exposes payload endpoint facts for compact-generator pullback on
sections.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source evaluation rectangles agree with the morphism target payload. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangles_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism =
      morphism.targetImportedRectangles :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles_eq_morphism_target
    morphism

/-- Pullback target evaluation rectangles agree with the morphism source payload. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangles_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism =
      morphism.sourceImportedRectangles :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles_eq_morphism_source
    morphism

/-- Pullback source evaluation imported count agrees with the morphism target count. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      morphism.targetImportedRectangleCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_morphism_target
    morphism

/-- Pullback target evaluation imported count agrees with the morphism source count. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      morphism.sourceImportedRectangleCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_morphism_source
    morphism

/-- Pullback source evaluation bookkeeping count agrees with the morphism target count. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationTraceBookkeepingCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        morphism =
      morphism.targetTraceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount_eq_morphism_target
    morphism

/-- Pullback target evaluation bookkeeping count agrees with the morphism source count. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationTraceBookkeepingCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        morphism =
      morphism.sourceTraceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount_eq_morphism_source
    morphism

/-- Pullback source evaluation rewrite count agrees with the morphism target count. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationRewriteStepCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        morphism =
      morphism.targetRewriteStepCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount_eq_morphism_target
    morphism

/-- Pullback target evaluation rewrite count agrees with the morphism source count. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationRewriteStepCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
        morphism =
      morphism.sourceRewriteStepCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount_eq_morphism_source
    morphism

/-- Pullback source evaluation imported count is counted by its rectangle list. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      (TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism).length :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_length
    morphism

/-- Pullback target evaluation imported count is counted by its rectangle list. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      (TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism).length :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_length
    morphism

/-- Pullback along identity has matching source and target rectangle payloads. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackIdentity_sourceTargetPayload
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        (𝟙 generator) =
      TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        (𝟙 generator) :=
  TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetPayload
    generator

/-- Pullback along identity has matching source and target imported counts. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackIdentity_sourceTargetPayloadCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        (𝟙 generator) =
      TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        (𝟙 generator) :=
  TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetPayloadCount
    generator

/-- Pullback along identity has matching source and target bookkeeping counts. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackIdentity_sourceTargetTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        (𝟙 generator) =
      TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        (𝟙 generator) :=
  TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetTraceBookkeepingCount
    generator

/-- Pullback along identity has matching source and target rewrite counts. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackIdentity_sourceTargetRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        (𝟙 generator) =
      TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
        (𝟙 generator) :=
  TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetRewriteStepCount
    generator

end AnalyticMotives
end LFunctions
end Boundary
