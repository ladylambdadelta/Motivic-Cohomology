import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.Owner

/-!
# Trace-calculus ledger counts for identity payload operations

This file records certificate-ledger formulas for bookkeeping and rewrite-step
counts when either the horizontal morphism or the vertical probe is an identity.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity horizontal northwest bookkeeping count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_bookkeeping_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal northeast bookkeeping count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_bookkeeping_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal southwest bookkeeping count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_bookkeeping_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal southeast bookkeeping count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_bookkeeping_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity vertical northwest bookkeeping count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northwest_bookkeeping_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical northeast bookkeeping count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northeast_bookkeeping_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical southwest bookkeeping count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_southwest_bookkeeping_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical southeast bookkeeping count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_southeast_bookkeeping_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.traceBookkeepingCount +
        probe.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity horizontal northwest rewrite count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_rewrite_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.northwestRewriteStepCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal northeast rewrite count is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_rewrite_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.northeastRewriteStepCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal southwest rewrite count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_rewrite_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.southwestRewriteStepCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal southeast rewrite count is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_rewrite_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.southeastRewriteStepCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity vertical northwest rewrite count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northwest_rewrite_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.northwestRewriteStepCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical northeast rewrite count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northeast_rewrite_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.northeastRewriteStepCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical southwest rewrite count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_southwest_rewrite_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.southwestRewriteStepCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical southeast rewrite count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_southeast_rewrite_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.rewriteStepCount +
        probe.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.southeastRewriteStepCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

end AnalyticMotives
end LFunctions
end Boundary
