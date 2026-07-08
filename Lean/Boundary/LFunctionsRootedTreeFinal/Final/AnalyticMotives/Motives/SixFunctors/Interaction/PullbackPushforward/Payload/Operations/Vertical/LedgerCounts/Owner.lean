import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Vertical.Owner

/-!
# Ledger counts for vertical pullback-pushforward payload operations

This file records certificate-ledger count formulas after vertical composition
in the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical composition northwest count is counted by source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northwest_count_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (left ≫ right) =
      source.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_northwest_count
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_certificateLedgers
      morphism
      right)

/-- Vertical composition northeast count is counted by target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northeast_count_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        (left ≫ right) =
      target.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_northeast_count
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_certificateLedgers
      morphism
      right)

/-- Vertical composition southwest count is counted by source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southwest_count_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        (left ≫ right) =
      source.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_southwest_count
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_certificateLedgers
      morphism
      left)

/-- Vertical composition southeast count is counted by target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southeast_count_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        (left ≫ right) =
      target.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_southeast_count
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_certificateLedgers
      morphism
      left)

end AnalyticMotives
end LFunctions
end Boundary
