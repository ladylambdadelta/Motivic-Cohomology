import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Lists.LedgerRectangles.Lengths.Owner

/-!
# Public length wrappers for pullback-pushforward square payloads

This file exposes count-as-list-length formulas for the four base corners of
the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicNorthwestCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    source.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.northwestCertificateLedgerImportedRectangles_length
    morphism
    probe

/-- Northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicNortheastCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    target.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.northeastCertificateLedgerImportedRectangles_length
    morphism
    probe

/-- Southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicSouthwestCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    source.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.southwestCertificateLedgerImportedRectangles_length
    morphism
    probe

/-- Southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicSoutheastCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    target.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.southeastCertificateLedgerImportedRectangles_length
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
