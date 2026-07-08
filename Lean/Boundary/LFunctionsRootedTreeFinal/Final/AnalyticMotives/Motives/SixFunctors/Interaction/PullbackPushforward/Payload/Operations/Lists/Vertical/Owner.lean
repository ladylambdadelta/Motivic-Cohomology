import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Owner

/-!
# Vertical list-level operations on pullback-pushforward payloads

This file records vertical-composition behavior for imported-rectangle lists
in the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical composition keeps the northwest rectangle list at the right probe target. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northwest_rectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        right :=
  congrArg₂
    List.append
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_sourceImportedRectangles
      left
      right)

/-- Vertical composition keeps the northeast rectangle list at the right probe target. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northeast_rectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        right :=
  congrArg₂
    List.append
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_sourceImportedRectangles
      left
      right)

/-- Vertical composition keeps the southwest rectangle list at the left probe source. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southwest_rectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        left :=
  congrArg₂
    List.append
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_targetImportedRectangles
      left
      right)

/-- Vertical composition keeps the southeast rectangle list at the left probe source. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southeast_rectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        (left ≫ right) =
      TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        left :=
  congrArg₂
    List.append
    rfl
    (TraceSixFunctorPullback.compactGenerator_comp_targetImportedRectangles
      left
      right)

end AnalyticMotives
end LFunctions
end Boundary
