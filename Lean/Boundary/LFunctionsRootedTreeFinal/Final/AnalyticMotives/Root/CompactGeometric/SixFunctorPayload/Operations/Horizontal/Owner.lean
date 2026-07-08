import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Horizontal.Owner

/-!
# Top-root horizontal pullback-pushforward operation payload

This file mirrors the motive-root horizontal-composition payload formulas under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root horizontal northwest rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_northwestImportedRectangleCount
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
  TraceAnalyticMotive.publicHorizontalComp_northwestImportedRectangleCount
    left
    right
    probe

/-- Top-root horizontal northeast rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_northeastImportedRectangleCount
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
  TraceAnalyticMotive.publicHorizontalComp_northeastImportedRectangleCount
    left
    right
    probe

/-- Top-root horizontal southwest rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_southwestImportedRectangleCount
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
  TraceAnalyticMotive.publicHorizontalComp_southwestImportedRectangleCount
    left
    right
    probe

/-- Top-root horizontal southeast rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_southeastImportedRectangleCount
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
  TraceAnalyticMotive.publicHorizontalComp_southeastImportedRectangleCount
    left
    right
    probe

/-- Top-root horizontal northwest rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_northwestImportedRectangles
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
  TraceAnalyticMotive.publicHorizontalComp_northwestImportedRectangles
    left
    right
    probe

/-- Top-root horizontal northeast rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_northeastImportedRectangles
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
  TraceAnalyticMotive.publicHorizontalComp_northeastImportedRectangles
    left
    right
    probe

/-- Top-root horizontal southwest rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_southwestImportedRectangles
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
  TraceAnalyticMotive.publicHorizontalComp_southwestImportedRectangles
    left
    right
    probe

/-- Top-root horizontal southeast rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_southeastImportedRectangles
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
  TraceAnalyticMotive.publicHorizontalComp_southeastImportedRectangles
    left
    right
    probe

/-- Top-root horizontal northwest bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_northwestTraceBookkeepingCount
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
  TraceAnalyticMotive.publicHorizontalComp_northwestTraceBookkeepingCount
    left
    right
    probe

/-- Top-root horizontal northeast bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_northeastTraceBookkeepingCount
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
  TraceAnalyticMotive.publicHorizontalComp_northeastTraceBookkeepingCount
    left
    right
    probe

/-- Top-root horizontal southwest bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_southwestTraceBookkeepingCount
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
  TraceAnalyticMotive.publicHorizontalComp_southwestTraceBookkeepingCount
    left
    right
    probe

/-- Top-root horizontal southeast bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_southeastTraceBookkeepingCount
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
  TraceAnalyticMotive.publicHorizontalComp_southeastTraceBookkeepingCount
    left
    right
    probe

/-- Top-root horizontal northwest rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_northwestRewriteStepCount
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
  TraceAnalyticMotive.publicHorizontalComp_northwestRewriteStepCount
    left
    right
    probe

/-- Top-root horizontal northeast rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_northeastRewriteStepCount
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
  TraceAnalyticMotive.publicHorizontalComp_northeastRewriteStepCount
    left
    right
    probe

/-- Top-root horizontal southwest rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_southwestRewriteStepCount
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
  TraceAnalyticMotive.publicHorizontalComp_southwestRewriteStepCount
    left
    right
    probe

/-- Top-root horizontal southeast rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicHorizontalComp_southeastRewriteStepCount
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
  TraceAnalyticMotive.publicHorizontalComp_southeastRewriteStepCount
    left
    right
    probe

end AnalyticMotives
end LFunctions
end Boundary
