import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.Operations.Horizontal.Lengths.Owner

/-!
# Horizontal operation wrappers for six-functor interactions

This aggregate owns the interaction-level horizontal operation branch.  The
current split content is the count-as-list-length certification surface for
horizontal pullback-pushforward operation payloads.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Horizontal composition northwest rectangle count is counted by the outer source and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_northwestImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestImportedRectangleCount
    left
    right
    probe

/-- Horizontal composition northeast rectangle count is counted by the outer target and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_northeastImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastImportedRectangleCount
    left
    right
    probe

/-- Horizontal composition southwest rectangle count is counted by the outer source and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_southwestImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestImportedRectangleCount
    left
    right
    probe

/-- Horizontal composition southeast rectangle count is counted by the outer target and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_southeastImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastImportedRectangleCount
    left
    right
    probe

/-- Horizontal composition northwest rectangle list is the outer source list followed by probe-target list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_northwestImportedRectangles
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestImportedRectangles
    left
    right
    probe

/-- Horizontal composition northeast rectangle list is the outer target list followed by probe-target list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_northeastImportedRectangles
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastImportedRectangles
    left
    right
    probe

/-- Horizontal composition southwest rectangle list is the outer source list followed by probe-source list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_southwestImportedRectangles
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestImportedRectangles
    left
    right
    probe

/-- Horizontal composition southeast rectangle list is the outer target list followed by probe-source list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_southeastImportedRectangles
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastImportedRectangles
    left
    right
    probe

/-- Horizontal composition northwest bookkeeping count is counted by the outer source and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_northwestTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestTraceBookkeepingCount
    left
    right
    probe

/-- Horizontal composition northeast bookkeeping count is counted by the outer target and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_northeastTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastTraceBookkeepingCount
    left
    right
    probe

/-- Horizontal composition southwest bookkeeping count is counted by the outer source and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_southwestTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestTraceBookkeepingCount
    left
    right
    probe

/-- Horizontal composition southeast bookkeeping count is counted by the outer target and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_southeastTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastTraceBookkeepingCount
    left
    right
    probe

/-- Horizontal composition northwest rewrite-step count is counted by the outer source and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_northwestRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestRewriteStepCount
    left
    right
    probe

/-- Horizontal composition northeast rewrite-step count is counted by the outer target and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_northeastRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastRewriteStepCount
    left
    right
    probe

/-- Horizontal composition southwest rewrite-step count is counted by the outer source and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_southwestRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestRewriteStepCount
    left
    right
    probe

/-- Horizontal composition southeast rewrite-step count is counted by the outer target and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_horizontalComp_southeastRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastRewriteStepCount
    left
    right
    probe

end AnalyticMotives
end LFunctions
end Boundary
