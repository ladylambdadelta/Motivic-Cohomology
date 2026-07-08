import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicPayload.Owner

/-!
# Motive-root pullback-pushforward square trace-calculus payload

This file mirrors the public four-corner trace-bookkeeping and rewrite-step
count formulas for the compact pullback-pushforward square under
`TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root northwest trace-bookkeeping count wrapper. -/
theorem TraceAnalyticMotive.publicNorthwestTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        probe =
      source.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicNorthwestTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root northeast trace-bookkeeping count wrapper. -/
theorem TraceAnalyticMotive.publicNortheastTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        probe =
      target.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicNortheastTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root southwest trace-bookkeeping count wrapper. -/
theorem TraceAnalyticMotive.publicSouthwestTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        probe =
      source.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicSouthwestTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root southeast trace-bookkeeping count wrapper. -/
theorem TraceAnalyticMotive.publicSoutheastTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        probe =
      target.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullbackPushforward.publicSoutheastTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root northwest rewrite-step count wrapper. -/
theorem TraceAnalyticMotive.publicNorthwestRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        probe =
      source.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicNorthwestRewriteStepCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root northeast rewrite-step count wrapper. -/
theorem TraceAnalyticMotive.publicNortheastRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        probe =
      target.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicNortheastRewriteStepCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root southwest rewrite-step count wrapper. -/
theorem TraceAnalyticMotive.publicSouthwestRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        probe =
      source.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicSouthwestRewriteStepCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root southeast rewrite-step count wrapper. -/
theorem TraceAnalyticMotive.publicSoutheastRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        probe =
      target.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullbackPushforward.publicSoutheastRewriteStepCount_eq_certificateLedgers
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
