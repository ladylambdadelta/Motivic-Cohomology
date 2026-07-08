import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Lists.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Mixed.Owner

/-!
# Mixed ledger rectangle lists for pullback-pushforward payload operations

This file records certificate-ledger rectangle-list formulas after simultaneous
horizontal and vertical composition in the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed northwest rectangle list is the left source ledger list followed by the right probe-target ledger list. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northwest_rectangles_eq_certificateLedgers
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
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_northwest_rectangles
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.northwestImportedRectangles_eq_certificateLedgers
      hLeft
      vRight)

/-- Mixed northeast rectangle list is the right target ledger list followed by the right probe-target ledger list. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northeast_rectangles_eq_certificateLedgers
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
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_northeast_rectangles
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.northeastImportedRectangles_eq_certificateLedgers
      hRight
      vRight)

/-- Mixed southwest rectangle list is the left source ledger list followed by the left probe-source ledger list. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southwest_rectangles_eq_certificateLedgers
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
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_southwest_rectangles
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.southwestImportedRectangles_eq_certificateLedgers
      hLeft
      vLeft)

/-- Mixed southeast rectangle list is the right target ledger list followed by the left probe-source ledger list. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southeast_rectangles_eq_certificateLedgers
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
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_southeast_rectangles
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.southeastImportedRectangles_eq_certificateLedgers
      hRight
      vLeft)

end AnalyticMotives
end LFunctions
end Boundary
