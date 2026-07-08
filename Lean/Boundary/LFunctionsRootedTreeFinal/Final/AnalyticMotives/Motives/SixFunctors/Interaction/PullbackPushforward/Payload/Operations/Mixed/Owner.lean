import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Vertical.Owner

/-!
# Mixed operations on pullback-pushforward square payloads

This file records the endpoint behavior of imported-rectangle counts when both
the horizontal morphism and the vertical probe in the compact
pullback-pushforward square are composed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed composition keeps northwest rectangle count at the left source and right probe target. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northwest_count
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        hLeft
        vRight :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northwest_count
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_northwest_count
      hLeft
      vLeft
      vRight)

/-- Mixed composition keeps northeast rectangle count at the right target and right probe target. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northeast_count
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        hRight
        vRight :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northeast_count
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_northeast_count
      hRight
      vLeft
      vRight)

/-- Mixed composition keeps southwest rectangle count at the left source and left probe source. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southwest_count
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        hLeft
        vLeft :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southwest_count
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_southwest_count
      hLeft
      vLeft
      vRight)

/-- Mixed composition keeps southeast rectangle count at the right target and left probe source. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southeast_count
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        hRight
        vLeft :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southeast_count
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_southeast_count
      hRight
      vLeft
      vRight)

end AnalyticMotives
end LFunctions
end Boundary
