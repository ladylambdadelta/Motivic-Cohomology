import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Identity.Vertical.Owner

/-!
# Motive-root vertical-identity pullback-pushforward operation payload

This file mirrors the public vertical-identity payload formulas for the compact
pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root vertical-identity northwest rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_northwestImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestImportedRectangleCount
    morphism
    probe

/-- Motive-root vertical-identity northeast rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_northeastImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastImportedRectangleCount
    morphism
    probe

/-- Motive-root vertical-identity southwest rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_southwestImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestImportedRectangleCount
    morphism
    probe

/-- Motive-root vertical-identity southeast rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_southeastImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastImportedRectangleCount
    morphism
    probe

/-- Motive-root vertical-identity northwest rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_northwestImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestImportedRectangles
    morphism
    probe

/-- Motive-root vertical-identity northeast rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_northeastImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastImportedRectangles
    morphism
    probe

/-- Motive-root vertical-identity southwest rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_southwestImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestImportedRectangles
    morphism
    probe

/-- Motive-root vertical-identity southeast rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_southeastImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastImportedRectangles
    morphism
    probe

/-- Motive-root vertical-identity northwest bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_northwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestTraceBookkeepingCount
    morphism
    probe

/-- Motive-root vertical-identity northeast bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_northeastTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastTraceBookkeepingCount
    morphism
    probe

/-- Motive-root vertical-identity southwest bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_southwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestTraceBookkeepingCount
    morphism
    probe

/-- Motive-root vertical-identity southeast bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_southeastTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastTraceBookkeepingCount
    morphism
    probe

/-- Motive-root vertical-identity northwest rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_northwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestRewriteStepCount
    morphism
    probe

/-- Motive-root vertical-identity northeast rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_northeastRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastRewriteStepCount
    morphism
    probe

/-- Motive-root vertical-identity southwest rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_southwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestRewriteStepCount
    morphism
    probe

/-- Motive-root vertical-identity southeast rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_southeastRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastRewriteStepCount
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
