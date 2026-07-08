import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Identity.Horizontal.Owner

/-!
# Top-root horizontal-identity pullback-pushforward operation payload

This file mirrors the motive-root horizontal-identity payload formulas under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root horizontal-identity northwest rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_northwestImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_northwestImportedRectangleCount
    generator
    probe

/-- Top-root horizontal-identity northeast rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_northeastImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_northeastImportedRectangleCount
    generator
    probe

/-- Top-root horizontal-identity southwest rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_southwestImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_southwestImportedRectangleCount
    generator
    probe

/-- Top-root horizontal-identity southeast rectangle count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_southeastImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_southeastImportedRectangleCount
    generator
    probe

/-- Top-root horizontal-identity northwest rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_northwestImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicIdentityHorizontal_northwestImportedRectangles
    generator
    probe

/-- Top-root horizontal-identity northeast rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_northeastImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicIdentityHorizontal_northeastImportedRectangles
    generator
    probe

/-- Top-root horizontal-identity southwest rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_southwestImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicIdentityHorizontal_southwestImportedRectangles
    generator
    probe

/-- Top-root horizontal-identity southeast rectangle-list wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_southeastImportedRectangles
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicIdentityHorizontal_southeastImportedRectangles
    generator
    probe

/-- Top-root horizontal-identity northwest bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_northwestTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_northwestTraceBookkeepingCount
    generator
    probe

/-- Top-root horizontal-identity northeast bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_northeastTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_northeastTraceBookkeepingCount
    generator
    probe

/-- Top-root horizontal-identity southwest bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_southwestTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_southwestTraceBookkeepingCount
    generator
    probe

/-- Top-root horizontal-identity southeast bookkeeping-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_southeastTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_southeastTraceBookkeepingCount
    generator
    probe

/-- Top-root horizontal-identity northwest rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_northwestRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_northwestRewriteStepCount
    generator
    probe

/-- Top-root horizontal-identity northeast rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_northeastRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_northeastRewriteStepCount
    generator
    probe

/-- Top-root horizontal-identity southwest rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_southwestRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_southwestRewriteStepCount
    generator
    probe

/-- Top-root horizontal-identity southeast rewrite-step-count wrapper. -/
theorem AnalyticMotivesRoot.publicIdentityHorizontal_southeastRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicIdentityHorizontal_southeastRewriteStepCount
    generator
    probe

end AnalyticMotives
end LFunctions
end Boundary
