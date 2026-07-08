import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Mixed.LedgerRectangles.Lengths.Owner

/-!
# Public length wrappers for mixed pullback-pushforward operations

This file exposes count-as-list-length formulas for simultaneous
horizontal-and-vertical composition payloads.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_northwestCertificateLedgerRectangles_length
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    hFirst.certificateLedger.importedRectangleCount +
        vThird.certificateLedger.importedRectangleCount =
      (hFirst.certificateLedger.importedRectangles ++
        vThird.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.mixedComp_northwest_certificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_northeastCertificateLedgerRectangles_length
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    hThird.certificateLedger.importedRectangleCount +
        vThird.certificateLedger.importedRectangleCount =
      (hThird.certificateLedger.importedRectangles ++
        vThird.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.mixedComp_northeast_certificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_southwestCertificateLedgerRectangles_length
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    hFirst.certificateLedger.importedRectangleCount +
        vFirst.certificateLedger.importedRectangleCount =
      (hFirst.certificateLedger.importedRectangles ++
        vFirst.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.mixedComp_southwest_certificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicMixedComp_southeastCertificateLedgerRectangles_length
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    hThird.certificateLedger.importedRectangleCount +
        vFirst.certificateLedger.importedRectangleCount =
      (hThird.certificateLedger.importedRectangles ++
        vFirst.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.mixedComp_southeast_certificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

end AnalyticMotives
end LFunctions
end Boundary
