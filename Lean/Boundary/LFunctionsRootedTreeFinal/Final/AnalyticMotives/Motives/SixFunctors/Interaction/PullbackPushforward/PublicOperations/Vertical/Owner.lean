import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Vertical.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Vertical.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.Vertical.LedgerCounts.Owner

/-!
# Public vertical-operation wrappers for the pullback-pushforward square

This file exposes vertical-composition payload formulas for the compact
pullback-pushforward square, normalized to endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical northwest rectangle count is counted by source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_northwest_count_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical northeast rectangle count is counted by target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_northeast_count_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical southwest rectangle count is counted by source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_southwest_count_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical southeast rectangle count is counted by target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastImportedRectangleCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_southeast_count_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical northwest rectangle list is the source list followed by right probe-target list. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestImportedRectangles
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
  TraceSixFunctorPullbackPushforward.verticalComp_northwest_rectangles_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical northeast rectangle list is the target list followed by right probe-target list. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastImportedRectangles
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
  TraceSixFunctorPullbackPushforward.verticalComp_northeast_rectangles_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical southwest rectangle list is the source list followed by left probe-source list. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestImportedRectangles
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
  TraceSixFunctorPullbackPushforward.verticalComp_southwest_rectangles_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical southeast rectangle list is the target list followed by left probe-source list. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastImportedRectangles
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
  TraceSixFunctorPullbackPushforward.verticalComp_southeast_rectangles_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical northwest bookkeeping count is counted by source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_northwest_bookkeeping_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical northeast bookkeeping count is counted by target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_northeast_bookkeeping_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical southwest bookkeeping count is counted by source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_southwest_bookkeeping_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical southeast bookkeeping count is counted by target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastTraceBookkeepingCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_southeast_bookkeeping_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical northwest rewrite-step count is counted by source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_northwest_rewrite_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical northeast rewrite-step count is counted by target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_northeast_rewrite_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical southwest rewrite-step count is counted by source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_southwest_rewrite_eq_certificateLedgers
    morphism
    left
    right

/-- Vertical southeast rewrite-step count is counted by target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastRewriteStepCount
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
  TraceSixFunctorPullbackPushforward.verticalComp_southeast_rewrite_eq_certificateLedgers
    morphism
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
