import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Identity.Horizontal.Owner

/-!
# Horizontal identity operation wrappers for six-functor interactions

This file exposes horizontal-identity pullback-pushforward payload formulas at
the interaction namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Horizontal identity northwest rectangle count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_northwestImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestImportedRectangleCount
    generator
    probe

/-- Horizontal identity northeast rectangle count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_northeastImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastImportedRectangleCount
    generator
    probe

/-- Horizontal identity southwest rectangle count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_southwestImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestImportedRectangleCount
    generator
    probe

/-- Horizontal identity southeast rectangle count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_southeastImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastImportedRectangleCount
    generator
    probe

/-- Horizontal identity northwest rectangle list is generator list followed by probe-target list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_northwestImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestImportedRectangles
    generator
    probe

/-- Horizontal identity northeast rectangle list is generator list followed by probe-target list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_northeastImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastImportedRectangles
    generator
    probe

/-- Horizontal identity southwest rectangle list is generator list followed by probe-source list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_southwestImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestImportedRectangles
    generator
    probe

/-- Horizontal identity southeast rectangle list is generator list followed by probe-source list. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_southeastImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastImportedRectangles
    generator
    probe

/-- Horizontal identity northwest bookkeeping count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_northwestTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestTraceBookkeepingCount
    generator
    probe

/-- Horizontal identity northeast bookkeeping count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_northeastTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastTraceBookkeepingCount
    generator
    probe

/-- Horizontal identity southwest bookkeeping count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_southwestTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestTraceBookkeepingCount
    generator
    probe

/-- Horizontal identity southeast bookkeeping count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_southeastTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastTraceBookkeepingCount
    generator
    probe

/-- Horizontal identity northwest rewrite-step count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_northwestRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestRewriteStepCount
    generator
    probe

/-- Horizontal identity northeast rewrite-step count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_northeastRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastRewriteStepCount
    generator
    probe

/-- Horizontal identity southwest rewrite-step count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_southwestRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestRewriteStepCount
    generator
    probe

/-- Horizontal identity southeast rewrite-step count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_identityHorizontal_southeastRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastRewriteStepCount
    generator
    probe

end AnalyticMotives
end LFunctions
end Boundary
