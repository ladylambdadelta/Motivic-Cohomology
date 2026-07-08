import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Vertical.LedgerRectangles.Lengths.Owner

/-!
# Public length wrappers for vertical pullback-pushforward operations

This file exposes count-as-list-length formulas for vertical-composition
operation payloads.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.verticalComp_northwest_certificateLedgerRectangles_length
    morphism
    left
    right

/-- Vertical northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    target.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.verticalComp_northeast_certificateLedgerRectangles_length
    morphism
    left
    right

/-- Vertical southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.verticalComp_southwest_certificateLedgerRectangles_length
    morphism
    left
    right

/-- Vertical southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    target.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.verticalComp_southeast_certificateLedgerRectangles_length
    morphism
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
