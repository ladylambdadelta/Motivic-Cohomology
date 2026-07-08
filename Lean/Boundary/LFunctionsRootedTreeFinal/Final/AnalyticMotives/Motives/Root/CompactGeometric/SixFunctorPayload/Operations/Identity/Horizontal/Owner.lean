import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Identity.Horizontal.Owner

/-!
# Motive-root horizontal-identity pullback-pushforward operation payload

This file mirrors the public horizontal-identity payload formulas for the
compact pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root horizontal-identity northwest rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_northwestImportedRectangleCount
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

/-- Motive-root horizontal-identity northeast rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_northeastImportedRectangleCount
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

/-- Motive-root horizontal-identity southwest rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_southwestImportedRectangleCount
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

/-- Motive-root horizontal-identity southeast rectangle count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_southeastImportedRectangleCount
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

/-- Motive-root horizontal-identity northwest rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_northwestImportedRectangles
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

/-- Motive-root horizontal-identity northeast rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_northeastImportedRectangles
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

/-- Motive-root horizontal-identity southwest rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_southwestImportedRectangles
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

/-- Motive-root horizontal-identity southeast rectangle-list wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_southeastImportedRectangles
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

/-- Motive-root horizontal-identity northwest bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_northwestTraceBookkeepingCount
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

/-- Motive-root horizontal-identity northeast bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_northeastTraceBookkeepingCount
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

/-- Motive-root horizontal-identity southwest bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_southwestTraceBookkeepingCount
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

/-- Motive-root horizontal-identity southeast bookkeeping-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_southeastTraceBookkeepingCount
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

/-- Motive-root horizontal-identity northwest rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_northwestRewriteStepCount
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

/-- Motive-root horizontal-identity northeast rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_northeastRewriteStepCount
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

/-- Motive-root horizontal-identity southwest rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_southwestRewriteStepCount
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

/-- Motive-root horizontal-identity southeast rewrite-step-count wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_southeastRewriteStepCount
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
