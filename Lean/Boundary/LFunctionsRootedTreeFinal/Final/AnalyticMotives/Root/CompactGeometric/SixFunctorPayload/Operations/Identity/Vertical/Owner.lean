import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Identity.Vertical.Owner

/-!
# Top-root vertical-identity pullback-pushforward operation payload

This file mirrors the motive-root vertical-identity payload formulas under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root vertical-identity northwest rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_northwestImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentityVertical_northwestImportedRectangleCount
    morphism
    probe

/-- Top-root vertical-identity northeast rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_northeastImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentityVertical_northeastImportedRectangleCount
    morphism
    probe

/-- Top-root vertical-identity southwest rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_southwestImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentityVertical_southwestImportedRectangleCount
    morphism
    probe

/-- Top-root vertical-identity southeast rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_southeastImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentityVertical_southeastImportedRectangleCount
    morphism
    probe

/-- Top-root vertical-identity northwest rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_northwestImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicIdentityVertical_northwestImportedRectangles
    morphism
    probe

/-- Top-root vertical-identity northeast rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_northeastImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicIdentityVertical_northeastImportedRectangles
    morphism
    probe

/-- Top-root vertical-identity southwest rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_southwestImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicIdentityVertical_southwestImportedRectangles
    morphism
    probe

/-- Top-root vertical-identity southeast rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_southeastImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicIdentityVertical_southeastImportedRectangles
    morphism
    probe

/-- Top-root vertical-identity northwest bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_northwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicIdentityVertical_northwestTraceBookkeepingCount
    morphism
    probe

/-- Top-root vertical-identity northeast bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_northeastTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicIdentityVertical_northeastTraceBookkeepingCount
    morphism
    probe

/-- Top-root vertical-identity southwest bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_southwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicIdentityVertical_southwestTraceBookkeepingCount
    morphism
    probe

/-- Top-root vertical-identity southeast bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_southeastTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicIdentityVertical_southeastTraceBookkeepingCount
    morphism
    probe

/-- Top-root vertical-identity northwest rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_northwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicIdentityVertical_northwestRewriteStepCount
    morphism
    probe

/-- Top-root vertical-identity northeast rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_northeastRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicIdentityVertical_northeastRewriteStepCount
    morphism
    probe

/-- Top-root vertical-identity southwest rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_southwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicIdentityVertical_southwestRewriteStepCount
    morphism
    probe

/-- Top-root vertical-identity southeast rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityVertical_southeastRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicIdentityVertical_southeastRewriteStepCount
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
