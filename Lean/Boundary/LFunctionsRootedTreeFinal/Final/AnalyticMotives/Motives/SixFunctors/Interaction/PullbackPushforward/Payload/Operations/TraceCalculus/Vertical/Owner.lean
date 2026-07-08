import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.Owner

/-!
# Vertical trace-calculus operations on pullback-pushforward payloads

This file records vertical-composition behavior for bookkeeping and rewrite
counts in the concrete compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical composition keeps northwest bookkeeping at the right probe target. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northwest_bookkeeping
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        right :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_sourceTraceBookkeepingCount
      left
      right)

/-- Vertical composition keeps northeast bookkeeping at the right probe target. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northeast_bookkeeping
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        right :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_sourceTraceBookkeepingCount
      left
      right)

/-- Vertical composition keeps southwest bookkeeping at the left probe source. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southwest_bookkeeping
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        left :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_targetTraceBookkeepingCount
      left
      right)

/-- Vertical composition keeps southeast bookkeeping at the left probe source. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southeast_bookkeeping
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        left :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_targetTraceBookkeepingCount
      left
      right)

/-- Vertical composition keeps northwest rewrite count at the right probe target. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northwest_rewrite
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        right :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_sourceRewriteStepCount
      left
      right)

/-- Vertical composition keeps northeast rewrite count at the right probe target. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northeast_rewrite
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        right :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_sourceRewriteStepCount
      left
      right)

/-- Vertical composition keeps southwest rewrite count at the left probe source. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southwest_rewrite
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        left :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_targetRewriteStepCount
      left
      right)

/-- Vertical composition keeps southeast rewrite count at the left probe source. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southeast_rewrite
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        left :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_targetRewriteStepCount
      left
      right)

end AnalyticMotives
end LFunctions
end Boundary
