import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Identity.Vertical.Owner

/-!
# Vertical identity length wrappers for six-functor interactions

This file exposes count-as-list-length certification for vertical identity
pullback-pushforward operation payloads at the interaction namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical identity northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_northwestImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestCertificateLedgerRectangles_length
    morphism
    probe

/-- Vertical identity northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_northeastImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastCertificateLedgerRectangles_length
    morphism
    probe

/-- Vertical identity southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_southwestImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestCertificateLedgerRectangles_length
    morphism
    probe

/-- Vertical identity southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_southeastImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastCertificateLedgerRectangles_length
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
