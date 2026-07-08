import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.LedgerRectangles.Owner

/-!
# Lengths of horizontal operation ledger rectangle lists

This file connects horizontal-composition certificate-ledger rectangle-list
formulas to horizontal-composition certificate-ledger count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Horizontal northwest ledger rectangle-list length is counted by the left source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northwest_certificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.horizontalComp_northwest_count_eq_certificateLedgers
        left
        right
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_length
        (left ≫ right)
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rectangles_eq_certificateLedgers
          left
          right
          probe)))

/-- Horizontal northeast ledger rectangle-list length is counted by the right target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northeast_certificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    third.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (third.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.horizontalComp_northeast_count_eq_certificateLedgers
        left
        right
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_length
        (left ≫ right)
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rectangles_eq_certificateLedgers
          left
          right
          probe)))

/-- Horizontal southwest ledger rectangle-list length is counted by the left source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southwest_certificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.horizontalComp_southwest_count_eq_certificateLedgers
        left
        right
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_length
        (left ≫ right)
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rectangles_eq_certificateLedgers
          left
          right
          probe)))

/-- Horizontal southeast ledger rectangle-list length is counted by the right target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southeast_certificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    third.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (third.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.horizontalComp_southeast_count_eq_certificateLedgers
        left
        right
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_length
        (left ≫ right)
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rectangles_eq_certificateLedgers
          left
          right
          probe)))

end AnalyticMotives
end LFunctions
end Boundary
