import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Mixed.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Mixed.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.Mixed.LedgerCounts.Owner

/-!
# Public mixed-operation wrappers for the pullback-pushforward square

This file exposes simultaneous horizontal-and-vertical composition payload
formulas for the compact pullback-pushforward square, normalized to endpoint
certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed northwest rectangle count is counted by left source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_northwestImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_northwest_count_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed northeast rectangle count is counted by right target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_northeastImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_northeast_count_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed southwest rectangle count is counted by left source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_southwestImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_southwest_count_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed southeast rectangle count is counted by right target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_southeastImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_southeast_count_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed northwest rectangle list is the left source list followed by right probe-target list. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_northwestImportedRectangles
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
  TraceSixFunctorPullbackPushforward.mixedComp_northwest_rectangles_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed northeast rectangle list is the right target list followed by right probe-target list. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_northeastImportedRectangles
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
  TraceSixFunctorPullbackPushforward.mixedComp_northeast_rectangles_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed southwest rectangle list is the left source list followed by left probe-source list. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_southwestImportedRectangles
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
  TraceSixFunctorPullbackPushforward.mixedComp_southwest_rectangles_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed southeast rectangle list is the right target list followed by left probe-source list. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_southeastImportedRectangles
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
  TraceSixFunctorPullbackPushforward.mixedComp_southeast_rectangles_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed northwest bookkeeping count is counted by left source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_northwestTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_northwest_bookkeeping_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed northeast bookkeeping count is counted by right target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_northeastTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_northeast_bookkeeping_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed southwest bookkeeping count is counted by left source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_southwestTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_southwest_bookkeeping_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed southeast bookkeeping count is counted by right target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_southeastTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_southeast_bookkeeping_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed northwest rewrite-step count is counted by left source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_northwestRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_northwest_rewrite_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed northeast rewrite-step count is counted by right target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_northeastRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_northeast_rewrite_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed southwest rewrite-step count is counted by left source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_southwestRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_southwest_rewrite_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed southeast rewrite-step count is counted by right target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_southeastRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.mixedComp_southeast_rewrite_eq_certificateLedgers
    hLeft
    hRight
    vLeft
    vRight

end AnalyticMotives
end LFunctions
end Boundary
