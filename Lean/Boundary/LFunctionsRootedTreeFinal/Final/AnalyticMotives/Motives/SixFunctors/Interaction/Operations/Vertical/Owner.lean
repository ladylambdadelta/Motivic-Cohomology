import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.Operations.Vertical.Lengths.Owner

/-!
# Vertical operation wrappers for six-functor interactions

This aggregate owns the interaction-level vertical operation branch.  The
current split content is the count-as-list-length certification surface for
vertical pullback-pushforward operation payloads.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical composition northwest rectangle count is counted by source and outer probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_northwestImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestImportedRectangleCount
    morphism
    left
    right

/-- Vertical composition northeast rectangle count is counted by target and outer probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_northeastImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastImportedRectangleCount
    morphism
    left
    right

/-- Vertical composition southwest rectangle count is counted by source and outer probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_southwestImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestImportedRectangleCount
    morphism
    left
    right

/-- Vertical composition southeast rectangle count is counted by target and outer probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_southeastImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastImportedRectangleCount
    morphism
    left
    right

/-- Vertical composition northwest rectangle list is source list followed by outer probe-target list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_northwestImportedRectangles
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
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestImportedRectangles
    morphism
    left
    right

/-- Vertical composition northeast rectangle list is target list followed by outer probe-target list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_northeastImportedRectangles
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
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastImportedRectangles
    morphism
    left
    right

/-- Vertical composition southwest rectangle list is source list followed by outer probe-source list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_southwestImportedRectangles
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
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestImportedRectangles
    morphism
    left
    right

/-- Vertical composition southeast rectangle list is target list followed by outer probe-source list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_southeastImportedRectangles
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
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastImportedRectangles
    morphism
    left
    right

/-- Vertical composition northwest bookkeeping count is counted by source and outer probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_northwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        (left ≫ right) =
      source.certificateLedger.traceBookkeepingCount +
        third.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestTraceBookkeepingCount
    morphism
    left
    right

/-- Vertical composition northeast bookkeeping count is counted by target and outer probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_northeastTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        (left ≫ right) =
      target.certificateLedger.traceBookkeepingCount +
        third.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastTraceBookkeepingCount
    morphism
    left
    right

/-- Vertical composition southwest bookkeeping count is counted by source and outer probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_southwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        (left ≫ right) =
      source.certificateLedger.traceBookkeepingCount +
        first.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestTraceBookkeepingCount
    morphism
    left
    right

/-- Vertical composition southeast bookkeeping count is counted by target and outer probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_southeastTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        (left ≫ right) =
      target.certificateLedger.traceBookkeepingCount +
        first.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastTraceBookkeepingCount
    morphism
    left
    right

/-- Vertical composition northwest rewrite-step count is counted by source and outer probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_northwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        (left ≫ right) =
      source.certificateLedger.rewriteStepCount +
        third.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestRewriteStepCount
    morphism
    left
    right

/-- Vertical composition northeast rewrite-step count is counted by target and outer probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_northeastRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        (left ≫ right) =
      target.certificateLedger.rewriteStepCount +
        third.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastRewriteStepCount
    morphism
    left
    right

/-- Vertical composition southwest rewrite-step count is counted by source and outer probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_southwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        (left ≫ right) =
      source.certificateLedger.rewriteStepCount +
        first.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestRewriteStepCount
    morphism
    left
    right

/-- Vertical composition southeast rewrite-step count is counted by target and outer probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_verticalComp_southeastRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        (left ≫ right) =
      target.certificateLedger.rewriteStepCount +
        first.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastRewriteStepCount
    morphism
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
