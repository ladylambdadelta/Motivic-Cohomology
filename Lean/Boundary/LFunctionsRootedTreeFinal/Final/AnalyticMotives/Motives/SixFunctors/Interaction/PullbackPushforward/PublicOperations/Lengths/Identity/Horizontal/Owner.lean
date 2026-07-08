import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Identity.LedgerRectangles.Lengths.Owner

/-!
# Public length wrappers for horizontal identity operations

This file exposes count-as-list-length formulas for horizontal identity
pullback-pushforward square payloads.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity-horizontal northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_certificateLedgerRectangles_length
    generator
    probe

/-- Identity-horizontal northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_certificateLedgerRectangles_length
    generator
    probe

/-- Identity-horizontal southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_certificateLedgerRectangles_length
    generator
    probe

/-- Identity-horizontal southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_certificateLedgerRectangles_length
    generator
    probe

end AnalyticMotives
end LFunctions
end Boundary
