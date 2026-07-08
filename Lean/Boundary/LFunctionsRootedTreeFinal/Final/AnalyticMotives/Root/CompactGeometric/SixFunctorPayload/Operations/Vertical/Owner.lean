import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Vertical.Owner

/-!
# Top-root vertical pullback-pushforward operation payload

This file mirrors the motive-root vertical-composition payload formulas under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root vertical northwest rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_northwestImportedRectangleCount
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
  TraceAnalyticMotive.publicVerticalComp_northwestImportedRectangleCount
    morphism
    left
    right

/-- Top-root vertical northeast rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_northeastImportedRectangleCount
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
  TraceAnalyticMotive.publicVerticalComp_northeastImportedRectangleCount
    morphism
    left
    right

/-- Top-root vertical southwest rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_southwestImportedRectangleCount
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
  TraceAnalyticMotive.publicVerticalComp_southwestImportedRectangleCount
    morphism
    left
    right

/-- Top-root vertical southeast rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_southeastImportedRectangleCount
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
  TraceAnalyticMotive.publicVerticalComp_southeastImportedRectangleCount
    morphism
    left
    right

/-- Top-root vertical northwest rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_northwestImportedRectangles
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
  TraceAnalyticMotive.publicVerticalComp_northwestImportedRectangles
    morphism
    left
    right

/-- Top-root vertical northeast rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_northeastImportedRectangles
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
  TraceAnalyticMotive.publicVerticalComp_northeastImportedRectangles
    morphism
    left
    right

/-- Top-root vertical southwest rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_southwestImportedRectangles
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
  TraceAnalyticMotive.publicVerticalComp_southwestImportedRectangles
    morphism
    left
    right

/-- Top-root vertical southeast rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_southeastImportedRectangles
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
  TraceAnalyticMotive.publicVerticalComp_southeastImportedRectangles
    morphism
    left
    right

/-- Top-root vertical northwest bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_northwestTraceBookkeepingCount
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
  TraceAnalyticMotive.publicVerticalComp_northwestTraceBookkeepingCount
    morphism
    left
    right

/-- Top-root vertical northeast bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_northeastTraceBookkeepingCount
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
  TraceAnalyticMotive.publicVerticalComp_northeastTraceBookkeepingCount
    morphism
    left
    right

/-- Top-root vertical southwest bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_southwestTraceBookkeepingCount
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
  TraceAnalyticMotive.publicVerticalComp_southwestTraceBookkeepingCount
    morphism
    left
    right

/-- Top-root vertical southeast bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_southeastTraceBookkeepingCount
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
  TraceAnalyticMotive.publicVerticalComp_southeastTraceBookkeepingCount
    morphism
    left
    right

/-- Top-root vertical northwest rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_northwestRewriteStepCount
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
  TraceAnalyticMotive.publicVerticalComp_northwestRewriteStepCount
    morphism
    left
    right

/-- Top-root vertical northeast rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_northeastRewriteStepCount
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
  TraceAnalyticMotive.publicVerticalComp_northeastRewriteStepCount
    morphism
    left
    right

/-- Top-root vertical southwest rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_southwestRewriteStepCount
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
  TraceAnalyticMotive.publicVerticalComp_southwestRewriteStepCount
    morphism
    left
    right

/-- Top-root vertical southeast rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicVerticalComp_southeastRewriteStepCount
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
  TraceAnalyticMotive.publicVerticalComp_southeastRewriteStepCount
    morphism
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
