import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Vertical.Owner

/-!
# Motive-root vertical pullback-pushforward operation payload

This file mirrors the public vertical-composition payload formulas for the
compact pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root vertical northwest rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_northwestImportedRectangleCount
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

/-- Motive-root vertical northeast rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_northeastImportedRectangleCount
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

/-- Motive-root vertical southwest rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_southwestImportedRectangleCount
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

/-- Motive-root vertical southeast rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_southeastImportedRectangleCount
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

/-- Motive-root vertical northwest rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_northwestImportedRectangles
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

/-- Motive-root vertical northeast rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_northeastImportedRectangles
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

/-- Motive-root vertical southwest rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_southwestImportedRectangles
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

/-- Motive-root vertical southeast rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_southeastImportedRectangles
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

/-- Motive-root vertical northwest bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_northwestTraceBookkeepingCount
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

/-- Motive-root vertical northeast bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_northeastTraceBookkeepingCount
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

/-- Motive-root vertical southwest bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_southwestTraceBookkeepingCount
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

/-- Motive-root vertical southeast bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_southeastTraceBookkeepingCount
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

/-- Motive-root vertical northwest rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_northwestRewriteStepCount
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

/-- Motive-root vertical northeast rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_northeastRewriteStepCount
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

/-- Motive-root vertical southwest rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_southwestRewriteStepCount
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

/-- Motive-root vertical southeast rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_southeastRewriteStepCount
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
