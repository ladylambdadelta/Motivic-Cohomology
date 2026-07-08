import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Owner

/-!
# Vertical operations on pullback-pushforward square payloads

This file records vertical-composition behavior for imported-rectangle counts
in the concrete compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical composition keeps the northwest rectangle count at the right probe target. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northwest_count
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        right :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_sourceImportedRectangleCount
      left
      right)

/-- Vertical composition keeps the northeast rectangle count at the right probe target. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northeast_count
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        right :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_sourceImportedRectangleCount
      left
      right)

/-- Vertical composition keeps the southwest rectangle count at the left probe source. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southwest_count
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        left :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_targetImportedRectangleCount
      left
      right)

/-- Vertical composition keeps the southeast rectangle count at the left probe source. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southeast_count
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        left :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_targetImportedRectangleCount
      left
      right)

end AnalyticMotives
end LFunctions
end Boundary
