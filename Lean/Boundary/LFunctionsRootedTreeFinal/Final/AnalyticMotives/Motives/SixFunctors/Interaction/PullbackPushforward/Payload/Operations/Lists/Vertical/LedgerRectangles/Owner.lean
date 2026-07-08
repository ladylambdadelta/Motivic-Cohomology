import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Lists.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Vertical.Owner

/-!
# Ledger rectangle lists for vertical list-level payload operations

This file records certificate-ledger rectangle-list formulas after vertical
composition in the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical composition northwest rectangle list is counted by the source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northwest_rectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        (left ≫ right) =
      source.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_northwest_rectangles
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.northwestImportedRectangles_eq_certificateLedgers
      morphism
      right)

/-- Vertical composition northeast rectangle list is counted by the target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northeast_rectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        (left ≫ right) =
      target.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_northeast_rectangles
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.northeastImportedRectangles_eq_certificateLedgers
      morphism
      right)

/-- Vertical composition southwest rectangle list is counted by the source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southwest_rectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        (left ≫ right) =
      source.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_southwest_rectangles
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.southwestImportedRectangles_eq_certificateLedgers
      morphism
      left)

/-- Vertical composition southeast rectangle list is counted by the target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southeast_rectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        (left ≫ right) =
      target.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_southeast_rectangles
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.southeastImportedRectangles_eq_certificateLedgers
      morphism
      left)

end AnalyticMotives
end LFunctions
end Boundary
