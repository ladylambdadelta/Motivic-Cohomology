import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Identity.Vertical.Owner

/-!
# Top-root vertical-identity pullback-pushforward operation lengths

This file mirrors the motive-root vertical-identity count-as-list-length
formulas under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root vertical-identity northwest rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_northwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentityVertical_northwestCertificateLedgerRectangles_length
    morphism
    probe

/-- Top-root vertical-identity northeast rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_northeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentityVertical_northeastCertificateLedgerRectangles_length
    morphism
    probe

/-- Top-root vertical-identity southwest rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_southwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentityVertical_southwestCertificateLedgerRectangles_length
    morphism
    probe

/-- Top-root vertical-identity southeast rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_southeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentityVertical_southeastCertificateLedgerRectangles_length
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
