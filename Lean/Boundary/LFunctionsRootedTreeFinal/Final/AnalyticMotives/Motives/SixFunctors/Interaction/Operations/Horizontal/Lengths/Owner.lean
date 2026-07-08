import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Owner

/-!
# Horizontal operation length wrappers for six-functor interactions

This file exposes count-as-list-length certification for horizontal
pullback-pushforward operation payloads at the interaction namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Horizontal composition northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_northwestImportedRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestCertificateLedgerRectangles_length
    left
    right
    probe

/-- Horizontal composition northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_northeastImportedRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    third.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (third.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastCertificateLedgerRectangles_length
    left
    right
    probe

/-- Horizontal composition southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_southwestImportedRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestCertificateLedgerRectangles_length
    left
    right
    probe

/-- Horizontal composition southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_southeastImportedRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    third.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (third.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastCertificateLedgerRectangles_length
    left
    right
    probe

end AnalyticMotives
end LFunctions
end Boundary
