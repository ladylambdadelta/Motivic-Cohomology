import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Mixed.Owner

/-!
# Motive-root mixed pullback-pushforward operation payload

This file mirrors the public simultaneous horizontal-and-vertical composition
payload formulas for the compact pullback-pushforward square under
`TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root mixed northwest rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_northwestImportedRectangleCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.importedRectangleCount +
        vThird.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_northwestImportedRectangleCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed northeast rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_northeastImportedRectangleCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.importedRectangleCount +
        vThird.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_northeastImportedRectangleCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed southwest rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_southwestImportedRectangleCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.importedRectangleCount +
        vFirst.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_southwestImportedRectangleCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed southeast rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_southeastImportedRectangleCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.importedRectangleCount +
        vFirst.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_southeastImportedRectangleCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed northwest rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_northwestImportedRectangles
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.importedRectangles ++
        vThird.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_northwestImportedRectangles
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed northeast rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_northeastImportedRectangles
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.importedRectangles ++
        vThird.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_northeastImportedRectangles
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed southwest rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_southwestImportedRectangles
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.importedRectangles ++
        vFirst.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_southwestImportedRectangles
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed southeast rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_southeastImportedRectangles
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.importedRectangles ++
        vFirst.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_southeastImportedRectangles
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed northwest bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_northwestTraceBookkeepingCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.traceBookkeepingCount +
        vThird.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_northwestTraceBookkeepingCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed northeast bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_northeastTraceBookkeepingCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.traceBookkeepingCount +
        vThird.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_northeastTraceBookkeepingCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed southwest bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_southwestTraceBookkeepingCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.traceBookkeepingCount +
        vFirst.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_southwestTraceBookkeepingCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed southeast bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_southeastTraceBookkeepingCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.traceBookkeepingCount +
        vFirst.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_southeastTraceBookkeepingCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed northwest rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_northwestRewriteStepCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.rewriteStepCount +
        vThird.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_northwestRewriteStepCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed northeast rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_northeastRewriteStepCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.rewriteStepCount +
        vThird.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_northeastRewriteStepCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed southwest rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_southwestRewriteStepCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.rewriteStepCount +
        vFirst.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_southwestRewriteStepCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root mixed southeast rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_southeastRewriteStepCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.rewriteStepCount +
        vFirst.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicMixedComp_southeastRewriteStepCount
    hLeft
    hRight
    vLeft
    vRight

end AnalyticMotives
end LFunctions
end Boundary
