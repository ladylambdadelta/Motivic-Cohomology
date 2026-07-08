import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Identity.LedgerRectangles.Lengths.Owner

/-!
# Public length wrappers for vertical identity operations

This file exposes count-as-list-length formulas for vertical identity
pullback-pushforward square payloads.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity-vertical northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.identityVertical_northwest_certificateLedgerRectangles_length
    morphism
    probe

/-- Identity-vertical northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.identityVertical_northeast_certificateLedgerRectangles_length
    morphism
    probe

/-- Identity-vertical southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.identityVertical_southwest_certificateLedgerRectangles_length
    morphism
    probe

/-- Identity-vertical southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.identityVertical_southeast_certificateLedgerRectangles_length
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
