import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Owner

/-!
# List-level operations on pullback-pushforward square payloads

This file records identity and composition behavior for the imported-rectangle
lists carried by the four corners of the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- If the horizontal morphism is identity, northwest and northeast rectangle lists agree. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_northeast_rectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        (𝟙 generator)
        probe =
      TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        (𝟙 generator)
        probe :=
  congrArg₂
    List.append
    (TraceSixFunctorPushforward.compactGenerator_id_sourceTargetImportedRectangles
      generator)
    rfl

/-- If the horizontal morphism is identity, southwest and southeast rectangle lists agree. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_southeast_rectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        (𝟙 generator)
        probe =
      TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        (𝟙 generator)
        probe :=
  congrArg₂
    List.append
    (TraceSixFunctorPushforward.compactGenerator_id_sourceTargetImportedRectangles
      generator)
    rfl

/-- If the vertical probe is identity, northwest and southwest rectangle lists agree. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northwest_southwest_rectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        (𝟙 probe) =
      TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        (𝟙 probe) :=
  congrArg₂
    List.append
    rfl
    (TraceSixFunctorPullback.compactGenerator_id_sourceTargetImportedRectangles
      probe)

/-- If the vertical probe is identity, northeast and southeast rectangle lists agree. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northeast_southeast_rectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        (𝟙 probe) =
      TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        (𝟙 probe) :=
  congrArg₂
    List.append
    rfl
    (TraceSixFunctorPullback.compactGenerator_id_sourceTargetImportedRectangles
      probe)

/-- Horizontal composition keeps the northwest rectangle list at the left source. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        left
        probe :=
  congrArg₂
    List.append
    (TraceSixFunctorPushforward.compactGenerator_comp_sourceImportedRectangles
      left
      right)
    rfl

/-- Horizontal composition keeps the northeast rectangle list at the right target. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        right
        probe :=
  congrArg₂
    List.append
    (TraceSixFunctorPushforward.compactGenerator_comp_targetImportedRectangles
      left
      right)
    rfl

/-- Horizontal composition keeps the southwest rectangle list at the left source. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        left
        probe :=
  congrArg₂
    List.append
    (TraceSixFunctorPushforward.compactGenerator_comp_sourceImportedRectangles
      left
      right)
    rfl

/-- Horizontal composition keeps the southeast rectangle list at the right target. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        right
        probe :=
  congrArg₂
    List.append
    (TraceSixFunctorPushforward.compactGenerator_comp_targetImportedRectangles
      left
      right)
    rfl

end AnalyticMotives
end LFunctions
end Boundary
