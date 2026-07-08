import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Identity.Horizontal.Owner

/-!
# Top-root horizontal-identity pullback-pushforward operation lengths

This file mirrors the motive-root horizontal-identity count-as-list-length
formulas under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root horizontal-identity northwest rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_northwestCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentityHorizontal_northwestCertificateLedgerRectangles_length
    generator
    probe

/-- Top-root horizontal-identity northeast rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_northeastCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentityHorizontal_northeastCertificateLedgerRectangles_length
    generator
    probe

/-- Top-root horizontal-identity southwest rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_southwestCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentityHorizontal_southwestCertificateLedgerRectangles_length
    generator
    probe

/-- Top-root horizontal-identity southeast rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_southeastCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentityHorizontal_southeastCertificateLedgerRectangles_length
    generator
    probe

end AnalyticMotives
end LFunctions
end Boundary
