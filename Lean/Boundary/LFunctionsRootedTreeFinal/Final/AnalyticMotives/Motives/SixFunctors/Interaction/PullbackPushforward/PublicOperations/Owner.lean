import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Mixed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Vertical.Owner

/-!
# Public operation wrappers for the pullback-pushforward square

This file exposes compact public names for the horizontal-composition operation
laws on the compact pullback-pushforward square and imports the identity and
length/mixed/vertical public operation children.  The lower payload-operation
owners prove the formulas; this file gives downstream code a stable surface
whose statements are already normalized to endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Horizontal northwest rectangle count is counted by the left source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.horizontalComp_northwest_count_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal northeast rectangle count is counted by the right target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.horizontalComp_northeast_count_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal southwest rectangle count is counted by the left source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.horizontalComp_southwest_count_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal southeast rectangle count is counted by the right target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.horizontalComp_southeast_count_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal northwest rectangle list is the left source list followed by probe-target list. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestImportedRectangles
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
  TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rectangles_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal northeast rectangle list is the right target list followed by probe-target list. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastImportedRectangles
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
  TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rectangles_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal southwest rectangle list is the left source list followed by probe-source list. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestImportedRectangles
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
  TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rectangles_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal southeast rectangle list is the right target list followed by probe-source list. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastImportedRectangles
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
  TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rectangles_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal northwest bookkeeping count is counted by the left source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (left ≫ right)
        probe =
      first.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.horizontalComp_northwest_bookkeeping_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal northeast bookkeeping count is counted by the right target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (left ≫ right)
        probe =
      third.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.horizontalComp_northeast_bookkeeping_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal southwest bookkeeping count is counted by the left source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (left ≫ right)
        probe =
      first.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.horizontalComp_southwest_bookkeeping_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal southeast bookkeeping count is counted by the right target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastTraceBookkeepingCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (left ≫ right)
        probe =
      third.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.horizontalComp_southeast_bookkeeping_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal northwest rewrite-step count is counted by the left source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (left ≫ right)
        probe =
      first.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rewrite_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal northeast rewrite-step count is counted by the right target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (left ≫ right)
        probe =
      third.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rewrite_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal southwest rewrite-step count is counted by the left source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (left ≫ right)
        probe =
      first.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rewrite_eq_certificateLedgers
    left
    right
    probe

/-- Horizontal southeast rewrite-step count is counted by the right target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastRewriteStepCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (left ≫ right)
        probe =
      third.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rewrite_eq_certificateLedgers
    left
    right
    probe

end AnalyticMotives
end LFunctions
end Boundary
