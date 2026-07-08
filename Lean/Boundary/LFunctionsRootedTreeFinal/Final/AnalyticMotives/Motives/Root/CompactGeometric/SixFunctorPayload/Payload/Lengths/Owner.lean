import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicPayload.Lengths.Owner

/-!
# Motive-root pullback-pushforward square payload lengths

This file mirrors the public four-corner count-as-list-length formulas for the
compact pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root northwest payload rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicNorthwestCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    source.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicNorthwestCertificateLedgerImportedRectangles_length
    morphism
    probe

/-- Motive-root northeast payload rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicNortheastCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    target.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicNortheastCertificateLedgerImportedRectangles_length
    morphism
    probe

/-- Motive-root southwest payload rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicSouthwestCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    source.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicSouthwestCertificateLedgerImportedRectangles_length
    morphism
    probe

/-- Motive-root southeast payload rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicSoutheastCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    target.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicSoutheastCertificateLedgerImportedRectangles_length
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
