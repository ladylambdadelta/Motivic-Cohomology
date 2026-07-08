import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Mixed.Owner

/-!
# Mixed operation length wrappers for six-functor interactions

This file exposes count-as-list-length certification for simultaneous
horizontal-and-vertical pullback-pushforward payloads at the interaction
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed composition northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_northwestImportedRectangles_length
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
  TraceSixFunctorPullbackPushforward.publicMixedComp_northwestCertificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed composition northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_northeastImportedRectangles_length
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
  TraceSixFunctorPullbackPushforward.publicMixedComp_northeastCertificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed composition southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_southwestImportedRectangles_length
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
  TraceSixFunctorPullbackPushforward.publicMixedComp_southwestCertificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

/-- Mixed composition southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_mixedComp_southeastImportedRectangles_length
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
  TraceSixFunctorPullbackPushforward.publicMixedComp_southeastCertificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

end AnalyticMotives
end LFunctions
end Boundary
