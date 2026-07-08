import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Horizontal.Owner

/-!
# Top-root horizontal pullback-pushforward operation lengths

This file mirrors the motive-root horizontal-composition count-as-list-length
formulas under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root horizontal northwest rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_northwestCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicHorizontalComp_northwestCertificateLedgerRectangles_length
    left
    right
    probe

/-- Top-root horizontal northeast rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_northeastCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    third.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (third.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicHorizontalComp_northeastCertificateLedgerRectangles_length
    left
    right
    probe

/-- Top-root horizontal southwest rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_southwestCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicHorizontalComp_southwestCertificateLedgerRectangles_length
    left
    right
    probe

/-- Top-root horizontal southeast rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_southeastCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    third.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (third.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicHorizontalComp_southeastCertificateLedgerRectangles_length
    left
    right
    probe

end AnalyticMotives
end LFunctions
end Boundary
