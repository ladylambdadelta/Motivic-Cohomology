import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner

/-!
# Payload endpoints for compact-generator pullback

Pullback on sections is induced by a compact-generator morphism.  This file
records the analytic endpoint payload at the target evaluation point and the
source evaluation point connected by that pullback.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source evaluation point of a pullback is the morphism target. -/
def TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  target.evaluationImportedRectangles

/-- The target evaluation point of a pullback is the morphism source. -/
def TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  source.evaluationImportedRectangles

/-- The source evaluation-point count of a pullback is the morphism target count. -/
def TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  target.evaluationImportedRectangleCount

/-- The target evaluation-point count of a pullback is the morphism source count. -/
def TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  source.evaluationImportedRectangleCount

/-- The source evaluation-point bookkeeping count of a pullback is the morphism target count. -/
def TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  target.evaluationTraceBookkeepingCount

/-- The target evaluation-point bookkeeping count of a pullback is the morphism source count. -/
def TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  source.evaluationTraceBookkeepingCount

/-- The source evaluation-point rewrite count of a pullback is the morphism target count. -/
def TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  target.evaluationRewriteStepCount

/-- The target evaluation-point rewrite count of a pullback is the morphism source count. -/
def TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    Nat :=
  source.evaluationRewriteStepCount

/-- Pullback source evaluation payload agrees with the morphism target endpoint payload. -/
theorem TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism =
      morphism.targetImportedRectangles :=
  rfl

/-- Pullback target evaluation payload agrees with the morphism source endpoint payload. -/
theorem TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism =
      morphism.sourceImportedRectangles :=
  rfl

/-- Pullback source evaluation count agrees with the morphism target endpoint count. -/
theorem TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      morphism.targetImportedRectangleCount :=
  rfl

/-- Pullback target evaluation count agrees with the morphism source endpoint count. -/
theorem TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      morphism.sourceImportedRectangleCount :=
  rfl

/-- Pullback source evaluation bookkeeping count agrees with the morphism target endpoint count. -/
theorem TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        morphism =
      morphism.targetTraceBookkeepingCount :=
  rfl

/-- Pullback target evaluation bookkeeping count agrees with the morphism source endpoint count. -/
theorem TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        morphism =
      morphism.sourceTraceBookkeepingCount :=
  rfl

/-- Pullback source evaluation rewrite count agrees with the morphism target endpoint count. -/
theorem TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount_eq_morphism_target
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        morphism =
      morphism.targetRewriteStepCount :=
  rfl

/-- Pullback target evaluation rewrite count agrees with the morphism source endpoint count. -/
theorem TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount_eq_morphism_source
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
        morphism =
      morphism.sourceRewriteStepCount :=
  rfl

/-- Pullback source evaluation count is counted by its rectangle list. -/
theorem TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      (TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism).length :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_length
    target

/-- Pullback target evaluation count is counted by its rectangle list. -/
theorem TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      (TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism).length :=
  TraceAnalyticGeometricGenerator.evaluationImportedRectangleCount_eq_length
    source

/-- Pullback along identity has the same source and target evaluation payload. -/
theorem TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetPayload
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        (𝟙 generator) =
      TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        (𝟙 generator) :=
  rfl

/-- Pullback along identity has the same source and target evaluation count. -/
theorem TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetPayloadCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        (𝟙 generator) =
      TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        (𝟙 generator) :=
  rfl

/-- Pullback along identity has the same source and target evaluation bookkeeping count. -/
theorem TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        (𝟙 generator) =
      TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        (𝟙 generator) :=
  rfl

/-- Pullback along identity has the same source and target evaluation rewrite count. -/
theorem TraceAnalyticGeometricGenerator.pullbackIdentity_sourceTargetRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        (𝟙 generator) =
      TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
        (𝟙 generator) :=
  rfl

/-- Pullback along a composite has source payload at the outer target. -/
theorem TraceAnalyticGeometricGenerator.pullbackComp_sourceEvaluationImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        (left ≫ right) =
      right.targetImportedRectangles :=
  rfl

/-- Pullback along a composite has target payload at the inner source. -/
theorem TraceAnalyticGeometricGenerator.pullbackComp_targetEvaluationImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        (left ≫ right) =
      left.sourceImportedRectangles :=
  rfl

/-- Pullback along a composite has source payload count at the outer target. -/
theorem TraceAnalyticGeometricGenerator.pullbackComp_sourceEvaluationImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        (left ≫ right) =
      right.targetImportedRectangleCount :=
  rfl

/-- Pullback along a composite has target payload count at the inner source. -/
theorem TraceAnalyticGeometricGenerator.pullbackComp_targetEvaluationImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        (left ≫ right) =
      left.sourceImportedRectangleCount :=
  rfl

/-- Pullback along a composite has source bookkeeping count at the outer target. -/
theorem TraceAnalyticGeometricGenerator.pullbackComp_sourceEvaluationTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationTraceBookkeepingCount
        (left ≫ right) =
      right.targetTraceBookkeepingCount :=
  rfl

/-- Pullback along a composite has target bookkeeping count at the inner source. -/
theorem TraceAnalyticGeometricGenerator.pullbackComp_targetEvaluationTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationTraceBookkeepingCount
        (left ≫ right) =
      left.sourceTraceBookkeepingCount :=
  rfl

/-- Pullback along a composite has source rewrite count at the outer target. -/
theorem TraceAnalyticGeometricGenerator.pullbackComp_sourceEvaluationRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        (left ≫ right) =
      right.targetRewriteStepCount :=
  rfl

/-- Pullback along a composite has target rewrite count at the inner source. -/
theorem TraceAnalyticGeometricGenerator.pullbackComp_targetEvaluationRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationRewriteStepCount
        (left ≫ right) =
      left.sourceRewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
