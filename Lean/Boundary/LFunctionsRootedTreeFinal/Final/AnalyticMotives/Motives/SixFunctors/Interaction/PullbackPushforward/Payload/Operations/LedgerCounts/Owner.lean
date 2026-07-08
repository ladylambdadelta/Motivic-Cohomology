import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Owner

/-!
# Ledger counts for horizontal pullback-pushforward payload operations

This file records certificate-ledger count formulas after horizontal
composition in the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Horizontal composition northwest count is counted by the left source and probe target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northwest_count_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (left ≫ right)
        probe =
      first.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northwest_count
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_certificateLedgers
      left
      probe)

/-- Horizontal composition northeast count is counted by the right target and probe target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northeast_count_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        (left ≫ right)
        probe =
      third.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northeast_count
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_certificateLedgers
      right
      probe)

/-- Horizontal composition southwest count is counted by the left source and probe source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southwest_count_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        (left ≫ right)
        probe =
      first.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southwest_count
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_certificateLedgers
      left
      probe)

/-- Horizontal composition southeast count is counted by the right target and probe source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southeast_count_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        (left ≫ right)
        probe =
      third.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southeast_count
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_certificateLedgers
      right
      probe)

end AnalyticMotives
end LFunctions
end Boundary
