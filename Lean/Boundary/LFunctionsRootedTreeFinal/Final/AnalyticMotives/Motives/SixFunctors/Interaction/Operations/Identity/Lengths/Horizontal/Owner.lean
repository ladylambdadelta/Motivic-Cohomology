import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Identity.Horizontal.Owner

/-!
# Horizontal identity length wrappers for six-functor interactions

This file exposes count-as-list-length certification for horizontal identity
pullback-pushforward operation payloads at the interaction namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Horizontal identity northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_northwestImportedRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestCertificateLedgerRectangles_length
    generator
    probe

/-- Horizontal identity northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_northeastImportedRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastCertificateLedgerRectangles_length
    generator
    probe

/-- Horizontal identity southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_southwestImportedRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestCertificateLedgerRectangles_length
    generator
    probe

/-- Horizontal identity southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_southeastImportedRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastCertificateLedgerRectangles_length
    generator
    probe

end AnalyticMotives
end LFunctions
end Boundary
