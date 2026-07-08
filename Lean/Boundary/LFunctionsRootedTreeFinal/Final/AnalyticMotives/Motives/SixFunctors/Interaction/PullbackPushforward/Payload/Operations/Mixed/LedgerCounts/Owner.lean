import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Mixed.Owner

/-!
# Ledger counts for mixed pullback-pushforward payload operations

This file records certificate-ledger formulas for imported-rectangle counts
after simultaneous horizontal and vertical composition in the compact
pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed northwest rectangle count is counted by left source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northwest_count_eq_certificateLedgers
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
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_northwest_count
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_certificateLedgers
      hLeft
      vRight)

/-- Mixed northeast rectangle count is counted by right target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northeast_count_eq_certificateLedgers
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
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_northeast_count
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_certificateLedgers
      hRight
      vRight)

/-- Mixed southwest rectangle count is counted by left source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southwest_count_eq_certificateLedgers
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
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_southwest_count
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_certificateLedgers
      hLeft
      vLeft)

/-- Mixed southeast rectangle count is counted by right target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southeast_count_eq_certificateLedgers
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
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_southeast_count
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_certificateLedgers
      hRight
      vLeft)

end AnalyticMotives
end LFunctions
end Boundary
