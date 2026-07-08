import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Mixed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Vertical.Owner

/-!
# Public length wrappers for horizontal pullback-pushforward operations

This file exposes count-as-list-length formulas for the public horizontal
operation payload of the compact pullback-pushforward square and imports the
public identity, mixed, and vertical length children.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Horizontal northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.horizontalComp_northwest_certificateLedgerRectangles_length
    left
    right
    probe

/-- Horizontal northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    third.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (third.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.horizontalComp_northeast_certificateLedgerRectangles_length
    left
    right
    probe

/-- Horizontal southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.horizontalComp_southwest_certificateLedgerRectangles_length
    left
    right
    probe

/-- Horizontal southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    third.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (third.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.horizontalComp_southeast_certificateLedgerRectangles_length
    left
    right
    probe

end AnalyticMotives
end LFunctions
end Boundary
