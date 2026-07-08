import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Mixed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.Operations.Mixed.Lengths.Owner

/-!
# Mixed operation wrappers for six-functor interactions

This file exposes simultaneous horizontal-and-vertical pullback-pushforward
payload formulas at the interaction namespace.  The pullback-pushforward public
operation owner proves the formulas; this file gives downstream interaction
code a small split surface so the root interaction owner stays below the line
cap.  Count-as-list-length certification lives in the `Lengths` child and is
re-exported here.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed composition northwest rectangle count is counted by left source and right probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_northwestImportedRectangleCount
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

/-- Mixed composition northeast rectangle count is counted by right target and right probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_northeastImportedRectangleCount
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

/-- Mixed composition southwest rectangle count is counted by left source and left probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_southwestImportedRectangleCount
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

/-- Mixed composition southeast rectangle count is counted by right target and left probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_southeastImportedRectangleCount
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

/-- Mixed composition northwest rectangle list is left source list followed by right probe-target list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_northwestImportedRectangles
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

/-- Mixed composition northeast rectangle list is right target list followed by right probe-target list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_northeastImportedRectangles
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

/-- Mixed composition southwest rectangle list is left source list followed by left probe-source list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_southwestImportedRectangles
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

/-- Mixed composition southeast rectangle list is right target list followed by left probe-source list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_southeastImportedRectangles
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

/-- Mixed composition northwest bookkeeping count is counted by left source and right probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_northwestTraceBookkeepingCount
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

/-- Mixed composition northeast bookkeeping count is counted by right target and right probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_northeastTraceBookkeepingCount
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

/-- Mixed composition southwest bookkeeping count is counted by left source and left probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_southwestTraceBookkeepingCount
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

/-- Mixed composition southeast bookkeeping count is counted by right target and left probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_southeastTraceBookkeepingCount
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

/-- Mixed composition northwest rewrite-step count is counted by left source and right probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_northwestRewriteStepCount
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

/-- Mixed composition northeast rewrite-step count is counted by right target and right probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_northeastRewriteStepCount
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

/-- Mixed composition southwest rewrite-step count is counted by left source and left probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_southwestRewriteStepCount
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

/-- Mixed composition southeast rewrite-step count is counted by right target and left probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_southeastRewriteStepCount
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
