import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Mixed.Owner

/-!
# Motive-root mixed pullback-pushforward operation lengths

This file mirrors the public mixed-composition count-as-list-length formulas
for the compact pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root mixed northwest rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_northwestCertificateLedgerRectangles_length
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

/-- Motive-root mixed northeast rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_northeastCertificateLedgerRectangles_length
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

/-- Motive-root mixed southwest rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_southwestCertificateLedgerRectangles_length
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

/-- Motive-root mixed southeast rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicMixedComp_southeastCertificateLedgerRectangles_length
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
