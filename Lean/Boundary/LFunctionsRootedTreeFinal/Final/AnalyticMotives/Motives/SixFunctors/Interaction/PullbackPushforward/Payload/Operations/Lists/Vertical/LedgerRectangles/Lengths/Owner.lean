import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Vertical.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Vertical.LedgerCounts.Owner

/-!
# Lengths of vertical operation ledger rectangle lists

This file connects vertical-composition certificate-ledger rectangle-list
formulas to vertical-composition certificate-ledger count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical northwest ledger rectangle-list length is counted by source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northwest_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.verticalComp_northwest_count_eq_certificateLedgers
        morphism
        left
        right))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_length
        morphism
        (left ≫ right))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.verticalComp_northwest_rectangles_eq_certificateLedgers
          morphism
          left
          right)))

/-- Vertical northeast ledger rectangle-list length is counted by target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northeast_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    target.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.verticalComp_northeast_count_eq_certificateLedgers
        morphism
        left
        right))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_length
        morphism
        (left ≫ right))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.verticalComp_northeast_rectangles_eq_certificateLedgers
          morphism
          left
          right)))

/-- Vertical southwest ledger rectangle-list length is counted by source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southwest_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.verticalComp_southwest_count_eq_certificateLedgers
        morphism
        left
        right))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_length
        morphism
        (left ≫ right))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.verticalComp_southwest_rectangles_eq_certificateLedgers
          morphism
          left
          right)))

/-- Vertical southeast ledger rectangle-list length is counted by target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southeast_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    target.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.verticalComp_southeast_count_eq_certificateLedgers
        morphism
        left
        right))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_length
        morphism
        (left ≫ right))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.verticalComp_southeast_rectangles_eq_certificateLedgers
          morphism
          left
          right)))

end AnalyticMotives
end LFunctions
end Boundary
