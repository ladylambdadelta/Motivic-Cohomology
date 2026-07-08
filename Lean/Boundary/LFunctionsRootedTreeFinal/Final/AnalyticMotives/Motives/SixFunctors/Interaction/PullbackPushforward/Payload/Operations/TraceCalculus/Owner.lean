import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.TraceCalculus.Owner

/-!
# Trace-calculus operations on pullback-pushforward square payloads

This file records identity and horizontal-composition behavior for the
bookkeeping and rewrite-step counts of the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- If the horizontal morphism is identity, northwest and northeast bookkeeping counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_northeast_bookkeeping
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (𝟙 generator)
        probe =
      TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (𝟙 generator)
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_id_sourceTargetTraceBookkeepingCount
      generator)
    rfl

/-- If the horizontal morphism is identity, northwest and northeast rewrite counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_northeast_rewrite
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (𝟙 generator)
        probe =
      TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (𝟙 generator)
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_id_sourceTargetRewriteStepCount
      generator)
    rfl

/-- If the horizontal morphism is identity, southwest and southeast bookkeeping counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_southeast_bookkeeping
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (𝟙 generator)
        probe =
      TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (𝟙 generator)
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_id_sourceTargetTraceBookkeepingCount
      generator)
    rfl

/-- If the horizontal morphism is identity, southwest and southeast rewrite counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_southeast_rewrite
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (𝟙 generator)
        probe =
      TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (𝟙 generator)
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_id_sourceTargetRewriteStepCount
      generator)
    rfl

/-- If the vertical probe is identity, northwest and southwest bookkeeping counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northwest_southwest_bookkeeping
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        (𝟙 probe) :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_id_sourceTargetTraceBookkeepingCount
      probe)

/-- If the vertical probe is identity, northwest and southwest rewrite counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northwest_southwest_rewrite
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        (𝟙 probe) =
      TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        (𝟙 probe) :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_id_sourceTargetRewriteStepCount
      probe)

/-- If the vertical probe is identity, northeast and southeast bookkeeping counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northeast_southeast_bookkeeping
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        (𝟙 probe) :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_id_sourceTargetTraceBookkeepingCount
      probe)

/-- If the vertical probe is identity, northeast and southeast rewrite counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northeast_southeast_rewrite
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        (𝟙 probe) =
      TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        (𝟙 probe) :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_id_sourceTargetRewriteStepCount
      probe)

/-- Horizontal composition keeps northwest bookkeeping at the left source. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northwest_bookkeeping
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        left
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_sourceTraceBookkeepingCount
      left
      right)
    rfl

/-- Horizontal composition keeps northeast bookkeeping at the right target. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northeast_bookkeeping
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        right
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_targetTraceBookkeepingCount
      left
      right)
    rfl

/-- Horizontal composition keeps southwest bookkeeping at the left source. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southwest_bookkeeping
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        left
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_sourceTraceBookkeepingCount
      left
      right)
    rfl

/-- Horizontal composition keeps southeast bookkeeping at the right target. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southeast_bookkeeping
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        right
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_targetTraceBookkeepingCount
      left
      right)
    rfl

/-- Horizontal composition keeps northwest rewrite count at the left source. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rewrite
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        left
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_sourceRewriteStepCount
      left
      right)
    rfl

/-- Horizontal composition keeps northeast rewrite count at the right target. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rewrite
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        right
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_targetRewriteStepCount
      left
      right)
    rfl

/-- Horizontal composition keeps southwest rewrite count at the left source. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rewrite
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        left
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_sourceRewriteStepCount
      left
      right)
    rfl

/-- Horizontal composition keeps southeast rewrite count at the right target. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rewrite
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        right
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_targetRewriteStepCount
      left
      right)
    rfl

end AnalyticMotives
end LFunctions
end Boundary
