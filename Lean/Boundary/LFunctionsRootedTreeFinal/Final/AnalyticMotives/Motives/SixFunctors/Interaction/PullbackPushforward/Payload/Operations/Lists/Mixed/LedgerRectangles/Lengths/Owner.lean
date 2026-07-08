import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Mixed.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Mixed.LedgerCounts.Owner

/-!
# Lengths of mixed ledger rectangle lists

This file connects mixed-composition certificate-ledger rectangle-list formulas
to mixed-composition certificate-ledger count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed northwest ledger rectangle-list length is counted by left source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northwest_certificateLedgerRectangles_length
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    hFirst.certificateLedger.importedRectangleCount +
        vThird.certificateLedger.importedRectangleCount =
      (hFirst.certificateLedger.importedRectangles ++
        vThird.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.mixedComp_northwest_count_eq_certificateLedgers
        hLeft
        hRight
        vLeft
        vRight))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_length
        (hLeft ≫ hRight)
        (vLeft ≫ vRight))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.mixedComp_northwest_rectangles_eq_certificateLedgers
          hLeft
          hRight
          vLeft
          vRight)))

/-- Mixed northeast ledger rectangle-list length is counted by right target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northeast_certificateLedgerRectangles_length
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    hThird.certificateLedger.importedRectangleCount +
        vThird.certificateLedger.importedRectangleCount =
      (hThird.certificateLedger.importedRectangles ++
        vThird.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.mixedComp_northeast_count_eq_certificateLedgers
        hLeft
        hRight
        vLeft
        vRight))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_length
        (hLeft ≫ hRight)
        (vLeft ≫ vRight))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.mixedComp_northeast_rectangles_eq_certificateLedgers
          hLeft
          hRight
          vLeft
          vRight)))

/-- Mixed southwest ledger rectangle-list length is counted by left source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southwest_certificateLedgerRectangles_length
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    hFirst.certificateLedger.importedRectangleCount +
        vFirst.certificateLedger.importedRectangleCount =
      (hFirst.certificateLedger.importedRectangles ++
        vFirst.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.mixedComp_southwest_count_eq_certificateLedgers
        hLeft
        hRight
        vLeft
        vRight))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_length
        (hLeft ≫ hRight)
        (vLeft ≫ vRight))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.mixedComp_southwest_rectangles_eq_certificateLedgers
          hLeft
          hRight
          vLeft
          vRight)))

/-- Mixed southeast ledger rectangle-list length is counted by right target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southeast_certificateLedgerRectangles_length
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    hThird.certificateLedger.importedRectangleCount +
        vFirst.certificateLedger.importedRectangleCount =
      (hThird.certificateLedger.importedRectangles ++
        vFirst.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.mixedComp_southeast_count_eq_certificateLedgers
        hLeft
        hRight
        vLeft
        vRight))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_length
        (hLeft ≫ hRight)
        (vLeft ≫ vRight))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.mixedComp_southeast_rectangles_eq_certificateLedgers
          hLeft
          hRight
          vLeft
          vRight)))

end AnalyticMotives
end LFunctions
end Boundary
