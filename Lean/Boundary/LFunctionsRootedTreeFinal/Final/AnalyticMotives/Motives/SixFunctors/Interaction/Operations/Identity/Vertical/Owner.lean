import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Identity.Vertical.Owner

/-!
# Vertical identity operation wrappers for six-functor interactions

This file exposes vertical-identity pullback-pushforward payload formulas at
the interaction namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical identity northwest rectangle count is counted by source and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_northwestImportedRectangleCount
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

/-- Vertical identity northeast rectangle count is counted by target and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_northeastImportedRectangleCount
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

/-- Vertical identity southwest rectangle count is counted by source and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_southwestImportedRectangleCount
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

/-- Vertical identity southeast rectangle count is counted by target and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_southeastImportedRectangleCount
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

/-- Vertical identity northwest rectangle list is source list followed by probe list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_northwestImportedRectangles
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

/-- Vertical identity northeast rectangle list is target list followed by probe list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_northeastImportedRectangles
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

/-- Vertical identity southwest rectangle list is source list followed by probe list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_southwestImportedRectangles
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

/-- Vertical identity southeast rectangle list is target list followed by probe list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_southeastImportedRectangles
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

/-- Vertical identity northwest bookkeeping count is counted by source and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_northwestTraceBookkeepingCount
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

/-- Vertical identity northeast bookkeeping count is counted by target and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_northeastTraceBookkeepingCount
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

/-- Vertical identity southwest bookkeeping count is counted by source and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_southwestTraceBookkeepingCount
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

/-- Vertical identity southeast bookkeeping count is counted by target and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_southeastTraceBookkeepingCount
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

/-- Vertical identity northwest rewrite-step count is counted by source and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_northwestRewriteStepCount
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

/-- Vertical identity northeast rewrite-step count is counted by target and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_northeastRewriteStepCount
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

/-- Vertical identity southwest rewrite-step count is counted by source and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_southwestRewriteStepCount
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

/-- Vertical identity southeast rewrite-step count is counted by target and probe ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityVertical_southeastRewriteStepCount
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
