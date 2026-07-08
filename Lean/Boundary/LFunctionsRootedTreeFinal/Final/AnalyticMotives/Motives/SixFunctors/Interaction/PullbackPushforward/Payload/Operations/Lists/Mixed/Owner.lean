import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Vertical.Owner

/-!
# Mixed list-level operations on pullback-pushforward payloads

This file records the endpoint behavior of imported-rectangle lists when both
the horizontal morphism and vertical probe are composed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed composition keeps northwest rectangle list at the left source and right probe target. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northwest_rectangles
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        hLeft
        vRight :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rectangles
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_northwest_rectangles
      hLeft
      vLeft
      vRight)

/-- Mixed composition keeps northeast rectangle list at the right target and right probe target. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northeast_rectangles
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        hRight
        vRight :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rectangles
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_northeast_rectangles
      hRight
      vLeft
      vRight)

/-- Mixed composition keeps southwest rectangle list at the left source and left probe source. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southwest_rectangles
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        hLeft
        vLeft :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rectangles
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_southwest_rectangles
      hLeft
      vLeft
      vRight)

/-- Mixed composition keeps southeast rectangle list at the right target and left probe source. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southeast_rectangles
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        hRight
        vLeft :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rectangles
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_southeast_rectangles
      hRight
      vLeft
      vRight)

end AnalyticMotives
end LFunctions
end Boundary
