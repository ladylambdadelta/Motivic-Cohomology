import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Mixed.Owner

/-!
# Top-root mixed pullback-pushforward operation lengths

This file mirrors the motive-root mixed-composition count-as-list-length
formulas under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root mixed northwest rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicMixedComp_northwestCertificateLedgerRectangles_length
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
  TraceAnalyticMotive.publicMixedComp_northwestCertificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

/-- Top-root mixed northeast rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicMixedComp_northeastCertificateLedgerRectangles_length
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
  TraceAnalyticMotive.publicMixedComp_northeastCertificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

/-- Top-root mixed southwest rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicMixedComp_southwestCertificateLedgerRectangles_length
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
  TraceAnalyticMotive.publicMixedComp_southwestCertificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

/-- Top-root mixed southeast rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicMixedComp_southeastCertificateLedgerRectangles_length
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
  TraceAnalyticMotive.publicMixedComp_southeastCertificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

end AnalyticMotives
end LFunctions
end Boundary
