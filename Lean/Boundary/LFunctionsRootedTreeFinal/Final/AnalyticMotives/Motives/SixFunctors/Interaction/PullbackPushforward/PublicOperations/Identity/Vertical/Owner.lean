import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.Identity.Owner

/-!
# Public vertical-identity operation wrappers

This file exposes the pullback-pushforward square payload formulas when the
vertical probe is an identity, normalized to certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity-vertical northwest rectangle count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_northwest_count_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical northeast rectangle count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_northeast_count_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical southwest rectangle count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_southwest_count_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical southeast rectangle count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_southeast_count_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical northwest rectangle list is source list followed by probe list. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.identityVertical_northwest_rectangles_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical northeast rectangle list is target list followed by probe list. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.identityVertical_northeast_rectangles_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical southwest rectangle list is source list followed by probe list. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.identityVertical_southwest_rectangles_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical southeast rectangle list is target list followed by probe list. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.identityVertical_southeast_rectangles_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical northwest bookkeeping count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_northwest_bookkeeping_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical northeast bookkeeping count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_northeast_bookkeeping_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical southwest bookkeeping count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_southwest_bookkeeping_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical southeast bookkeeping count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_southeast_bookkeeping_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical northwest rewrite-step count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_northwest_rewrite_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical northeast rewrite-step count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_northeast_rewrite_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical southwest rewrite-step count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_southwest_rewrite_eq_certificateLedgers
    morphism
    probe

/-- Identity-vertical southeast rewrite-step count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.identityVertical_southeast_rewrite_eq_certificateLedgers
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
