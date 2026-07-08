import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.Owner

/-!
# Payload for compact-generator pullback functional

This file records the imported finite-rectangle endpoint payload attached to
the concrete compact-generator pullback functional.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source evaluation payload of the compact-generator pullback functional. -/
def TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
    morphism

/-- Target evaluation payload of the compact-generator pullback functional. -/
def TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
    morphism

/-- Source evaluation payload count of the compact-generator pullback functional. -/
def TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
    morphism

/-- Target evaluation payload count of the compact-generator pullback functional. -/
def TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
    morphism

/-- Source evaluation bookkeeping count of the compact-generator pullback functional. -/
def TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
    morphism

/-- Target evaluation bookkeeping count of the compact-generator pullback functional. -/
def TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
    morphism

/-- Source evaluation rewrite count of the compact-generator pullback functional. -/
def TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
    morphism

/-- Target evaluation rewrite count of the compact-generator pullback functional. -/
def TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
    morphism

/-- Pullback functional source payload agrees with the morphism target endpoint. -/
theorem TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles morphism =
      morphism.targetImportedRectangles :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles_eq_morphism_target
    morphism

/-- Pullback functional target payload agrees with the morphism source endpoint. -/
theorem TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles morphism =
      morphism.sourceImportedRectangles :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles_eq_morphism_source
    morphism

/-- Pullback functional source payload count agrees with the morphism target endpoint count. -/
theorem TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount morphism =
      morphism.targetImportedRectangleCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_morphism_target
    morphism

/-- Pullback functional target payload count agrees with the morphism source endpoint count. -/
theorem TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount morphism =
      morphism.sourceImportedRectangleCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_morphism_source
    morphism

/-- Pullback functional source bookkeeping count agrees with the morphism target endpoint. -/
theorem TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount morphism =
      morphism.targetTraceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount_eq_morphism_target
    morphism

/-- Pullback functional target bookkeeping count agrees with the morphism source endpoint. -/
theorem TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount morphism =
      morphism.sourceTraceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount_eq_morphism_source
    morphism

/-- Pullback functional source rewrite count agrees with the morphism target endpoint. -/
theorem TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount morphism =
      morphism.targetRewriteStepCount :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount_eq_morphism_target
    morphism

/-- Pullback functional target rewrite count agrees with the morphism source endpoint. -/
theorem TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount morphism =
      morphism.sourceRewriteStepCount :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount_eq_morphism_source
    morphism

/-- Pullback functional source payload count is counted by its rectangle list. -/
theorem TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount morphism =
      (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles
        morphism).length :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_length
    morphism

/-- Pullback functional target payload count is counted by its rectangle list. -/
theorem TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount morphism =
      (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles
        morphism).length :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_length
    morphism

/-- Identity pullback has matching source and target payload rectangles. -/
theorem TraceSixFunctorPullback.compactGenerator_id_sourceTargetImportedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles
        (𝟙 generator) =
      TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles
        (𝟙 generator) :=
  TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetPayload
    generator

/-- Identity pullback has matching source and target payload counts. -/
theorem TraceSixFunctorPullback.compactGenerator_id_sourceTargetImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount
        (𝟙 generator) =
      TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount
        (𝟙 generator) :=
  TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetPayloadCount
    generator

/-- Identity pullback has matching source and target bookkeeping counts. -/
theorem TraceSixFunctorPullback.compactGenerator_id_sourceTargetTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount
        (𝟙 generator) =
      TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount
        (𝟙 generator) :=
  TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetTraceBookkeepingCount
    generator

/-- Identity pullback has matching source and target rewrite counts. -/
theorem TraceSixFunctorPullback.compactGenerator_id_sourceTargetRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount
        (𝟙 generator) =
      TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount
        (𝟙 generator) :=
  TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetRewriteStepCount
    generator

/-- Composed pullback source payload is the right morphism target endpoint payload. -/
theorem TraceSixFunctorPullback.compactGenerator_comp_sourceImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles
        (left ≫ right) =
      right.targetImportedRectangles :=
  TraceAnalyticGeometricGenerator.pullbackComp_sourceEvaluationImportedRectangles
    left
    right

/-- Composed pullback target payload is the left morphism source endpoint payload. -/
theorem TraceSixFunctorPullback.compactGenerator_comp_targetImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles
        (left ≫ right) =
      left.sourceImportedRectangles :=
  TraceAnalyticGeometricGenerator.pullbackComp_targetEvaluationImportedRectangles
    left
    right

/-- Composed pullback source payload count is the right morphism target endpoint count. -/
theorem TraceSixFunctorPullback.compactGenerator_comp_sourceImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount
        (left ≫ right) =
      right.targetImportedRectangleCount :=
  TraceAnalyticGeometricGenerator.pullbackComp_sourceEvaluationImportedRectangleCount
    left
    right

/-- Composed pullback target payload count is the left morphism source endpoint count. -/
theorem TraceSixFunctorPullback.compactGenerator_comp_targetImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount
        (left ≫ right) =
      left.sourceImportedRectangleCount :=
  TraceAnalyticGeometricGenerator.pullbackComp_targetEvaluationImportedRectangleCount
    left
    right

/-- Composed pullback source bookkeeping count is the right morphism target endpoint count. -/
theorem TraceSixFunctorPullback.compactGenerator_comp_sourceTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount
        (left ≫ right) =
      right.targetTraceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.pullbackComp_sourceEvaluationTraceBookkeepingCount
    left
    right

/-- Composed pullback target bookkeeping count is the left morphism source endpoint count. -/
theorem TraceSixFunctorPullback.compactGenerator_comp_targetTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount
        (left ≫ right) =
      left.sourceTraceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.pullbackComp_targetEvaluationTraceBookkeepingCount
    left
    right

/-- Composed pullback source rewrite count is the right morphism target endpoint count. -/
theorem TraceSixFunctorPullback.compactGenerator_comp_sourceRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount
        (left ≫ right) =
      right.targetRewriteStepCount :=
  TraceAnalyticGeometricGenerator.pullbackComp_sourceEvaluationRewriteStepCount
    left
    right

/-- Composed pullback target rewrite count is the left morphism source endpoint count. -/
theorem TraceSixFunctorPullback.compactGenerator_comp_targetRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount
        (left ≫ right) =
      left.sourceRewriteStepCount :=
  TraceAnalyticGeometricGenerator.pullbackComp_targetEvaluationRewriteStepCount
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
