import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.Identity.Owner

/-!
# Public horizontal-identity operation wrappers

This file exposes the pullback-pushforward square payload formulas when the
horizontal morphism is an identity, normalized to certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity-horizontal northwest rectangle count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_count_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal northeast rectangle count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_count_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal southwest rectangle count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_count_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal southeast rectangle count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_count_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal northwest rectangle list is generator list followed by probe-target list. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_rectangles_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal northeast rectangle list is generator list followed by probe-target list. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_rectangles_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal southwest rectangle list is generator list followed by probe-source list. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_rectangles_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal southeast rectangle list is generator list followed by probe-source list. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_rectangles_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal northwest bookkeeping count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_bookkeeping_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal northeast bookkeeping count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_bookkeeping_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal southwest bookkeeping count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_bookkeeping_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal southeast bookkeeping count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_bookkeeping_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal northwest rewrite-step count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_rewrite_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal northeast rewrite-step count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_rewrite_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal southwest rewrite-step count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_rewrite_eq_certificateLedgers
    generator
    probe

/-- Identity-horizontal southeast rewrite-step count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_rewrite_eq_certificateLedgers
    generator
    probe

end AnalyticMotives
end LFunctions
end Boundary
