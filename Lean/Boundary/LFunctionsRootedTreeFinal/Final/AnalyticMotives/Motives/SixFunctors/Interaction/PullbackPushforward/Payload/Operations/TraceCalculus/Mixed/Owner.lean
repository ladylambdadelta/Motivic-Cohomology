import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.Vertical.Owner

/-!
# Mixed trace-calculus operations on pullback-pushforward payloads

This file records the endpoint behavior of bookkeeping and rewrite-step counts
when both the horizontal morphism and the vertical probe are composed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed composition keeps northwest bookkeeping at the left source and right probe target. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northwest_bookkeeping
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        hLeft
        vRight :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northwest_bookkeeping
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_northwest_bookkeeping
      hLeft
      vLeft
      vRight)

/-- Mixed composition keeps northeast bookkeeping at the right target and right probe target. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northeast_bookkeeping
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        hRight
        vRight :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northeast_bookkeeping
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_northeast_bookkeeping
      hRight
      vLeft
      vRight)

/-- Mixed composition keeps southwest bookkeeping at the left source and left probe source. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southwest_bookkeeping
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        hLeft
        vLeft :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southwest_bookkeeping
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_southwest_bookkeeping
      hLeft
      vLeft
      vRight)

/-- Mixed composition keeps southeast bookkeeping at the right target and left probe source. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southeast_bookkeeping
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        hRight
        vLeft :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southeast_bookkeeping
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_southeast_bookkeeping
      hRight
      vLeft
      vRight)

/-- Mixed composition keeps northwest rewrite count at the left source and right probe target. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northwest_rewrite
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        hLeft
        vRight :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rewrite
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_northwest_rewrite
      hLeft
      vLeft
      vRight)

/-- Mixed composition keeps northeast rewrite count at the right target and right probe target. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northeast_rewrite
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        hRight
        vRight :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rewrite
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_northeast_rewrite
      hRight
      vLeft
      vRight)

/-- Mixed composition keeps southwest rewrite count at the left source and left probe source. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southwest_rewrite
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        hLeft
        vLeft :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rewrite
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_southwest_rewrite
      hLeft
      vLeft
      vRight)

/-- Mixed composition keeps southeast rewrite count at the right target and left probe source. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southeast_rewrite
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        hRight
        vLeft :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rewrite
      hLeft
      hRight
      (vLeft ≫ vRight))
    (TraceSixFunctorPullbackPushforward.verticalComp_southeast_rewrite
      hRight
      vLeft
      vRight)

end AnalyticMotives
end LFunctions
end Boundary
