import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Lists.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Owner

/-!
# Ledger rectangle lists for list-level payload operations

This file records certificate-ledger rectangle-list formulas after horizontal
composition in the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Horizontal composition northwest rectangle list is counted by the left source and probe target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rectangles_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        (left ≫ right)
        probe =
      first.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rectangles
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.northwestImportedRectangles_eq_certificateLedgers
      left
      probe)

/-- Horizontal composition northeast rectangle list is counted by the right target and probe target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rectangles_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        (left ≫ right)
        probe =
      third.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rectangles
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.northeastImportedRectangles_eq_certificateLedgers
      right
      probe)

/-- Horizontal composition southwest rectangle list is counted by the left source and probe source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rectangles_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        (left ≫ right)
        probe =
      first.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rectangles
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.southwestImportedRectangles_eq_certificateLedgers
      left
      probe)

/-- Horizontal composition southeast rectangle list is counted by the right target and probe source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rectangles_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        (left ≫ right)
        probe =
      third.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rectangles
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.southeastImportedRectangles_eq_certificateLedgers
      right
      probe)

end AnalyticMotives
end LFunctions
end Boundary
