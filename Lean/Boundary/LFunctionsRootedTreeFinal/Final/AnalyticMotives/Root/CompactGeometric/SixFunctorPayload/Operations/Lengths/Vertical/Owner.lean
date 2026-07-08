import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Vertical.Owner

/-!
# Top-root vertical pullback-pushforward operation lengths

This file mirrors the motive-root vertical-composition count-as-list-length
formulas under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root vertical northwest rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_northwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicVerticalComp_northwestCertificateLedgerRectangles_length
    morphism
    left
    right

/-- Top-root vertical northeast rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_northeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    target.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicVerticalComp_northeastCertificateLedgerRectangles_length
    morphism
    left
    right

/-- Top-root vertical southwest rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_southwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicVerticalComp_southwestCertificateLedgerRectangles_length
    morphism
    left
    right

/-- Top-root vertical southeast rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_southeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    target.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicVerticalComp_southeastCertificateLedgerRectangles_length
    morphism
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
