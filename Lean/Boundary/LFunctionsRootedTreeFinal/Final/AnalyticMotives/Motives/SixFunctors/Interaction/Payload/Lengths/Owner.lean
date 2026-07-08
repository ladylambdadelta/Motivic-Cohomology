import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicPayload.Lengths.Owner

/-!
# Base payload length wrappers for six-functor interactions

This file exposes count-as-list-length certification for the four base corners
of the pullback-pushforward interaction payload.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback-pushforward northwest rectangle count is the northwest rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_northwestImportedRectangles_length
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

/-- Pullback-pushforward northeast rectangle count is the northeast rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_northeastImportedRectangles_length
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

/-- Pullback-pushforward southwest rectangle count is the southwest rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_southwestImportedRectangles_length
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

/-- Pullback-pushforward southeast rectangle count is the southeast rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_southeastImportedRectangles_length
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
