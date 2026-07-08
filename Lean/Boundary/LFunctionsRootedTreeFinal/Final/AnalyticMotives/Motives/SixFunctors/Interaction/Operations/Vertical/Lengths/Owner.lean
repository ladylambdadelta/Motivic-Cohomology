import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Vertical.Owner

/-!
# Vertical operation length wrappers for six-functor interactions

This file exposes count-as-list-length certification for vertical
pullback-pushforward operation payloads at the interaction namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical composition northwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_northwestImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestCertificateLedgerRectangles_length
    morphism
    left
    right

/-- Vertical composition northeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_northeastImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    target.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastCertificateLedgerRectangles_length
    morphism
    left
    right

/-- Vertical composition southwest certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_southwestImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestCertificateLedgerRectangles_length
    morphism
    left
    right

/-- Vertical composition southeast certificate-ledger rectangle count is its rectangle-list length. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_southeastImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    target.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastCertificateLedgerRectangles_length
    morphism
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
