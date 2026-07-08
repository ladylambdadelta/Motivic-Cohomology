import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Payload.Lengths.Owner

/-!
# Top-root pullback-pushforward square payload lengths

This file mirrors the motive-root four-corner count-as-list-length formulas for
the compact pullback-pushforward square under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root northwest payload rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicNorthwestCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    source.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicNorthwestCertificateLedgerImportedRectangles_length
    morphism
    probe

/-- Top-root northeast payload rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicNortheastCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    target.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicNortheastCertificateLedgerImportedRectangles_length
    morphism
    probe

/-- Top-root southwest payload rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicSouthwestCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    source.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicSouthwestCertificateLedgerImportedRectangles_length
    morphism
    probe

/-- Top-root southeast payload rectangle-count-as-length wrapper. -/
theorem AnalyticMotivesRoot.publicSoutheastCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    target.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicSoutheastCertificateLedgerImportedRectangles_length
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
