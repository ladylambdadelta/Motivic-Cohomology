import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Owner

/-!
# Operations on pullback-pushforward square payloads

This file records identity and composition behavior for the concrete corner
payload counts of the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- If the horizontal morphism is identity, northwest and northeast rectangle counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_northeast_count
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (𝟙 generator)
        probe =
      TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        (𝟙 generator)
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_id_sourceTargetImportedRectangleCount
      generator)
    rfl

/-- If the horizontal morphism is identity, southwest and southeast rectangle counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_southeast_count
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        (𝟙 generator)
        probe =
      TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        (𝟙 generator)
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_id_sourceTargetImportedRectangleCount
      generator)
    rfl

/-- If the vertical probe is identity, northwest and southwest rectangle counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northwest_southwest_count
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        (𝟙 probe) :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_id_sourceTargetImportedRectangleCount
      probe)

/-- If the vertical probe is identity, northeast and southeast rectangle counts agree. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northeast_southeast_count
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        (𝟙 probe) =
      TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        (𝟙 probe) :=
  congrArg₂
    Nat.add
    rfl
    (TraceSixFunctorPullback.compactGenerator_id_sourceTargetImportedRectangleCount
      probe)

/-- Horizontal composition keeps the northwest rectangle count at the left source. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northwest_count
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        left
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_sourceImportedRectangleCount
      left
      right)
    rfl

/-- Horizontal composition keeps the northeast rectangle count at the right target. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northeast_count
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        right
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_targetImportedRectangleCount
      left
      right)
    rfl

/-- Horizontal composition keeps the southwest rectangle count at the left source. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southwest_count
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        left
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_sourceImportedRectangleCount
      left
      right)
    rfl

/-- Horizontal composition keeps the southeast rectangle count at the right target. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southeast_count
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        (left ≫ right)
        probe =
      TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        right
        probe :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGenerator_comp_targetImportedRectangleCount
      left
      right)
    rfl

end AnalyticMotives
end LFunctions
end Boundary
