import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicPayload.Owner

/-!
# Base trace-calculus payload wrappers for six-functor interactions

This file exposes trace-bookkeeping and rewrite-step count formulas for the
four base corners of the pullback-pushforward interaction payload.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback-pushforward northwest bookkeeping count is counted by source and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_northwestTraceBookkeepingCount
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

/-- Pullback-pushforward northeast bookkeeping count is counted by target and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_northeastTraceBookkeepingCount
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

/-- Pullback-pushforward southwest bookkeeping count is counted by source and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_southwestTraceBookkeepingCount
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

/-- Pullback-pushforward southeast bookkeeping count is counted by target and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_southeastTraceBookkeepingCount
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

/-- Pullback-pushforward northwest rewrite-step count is counted by source and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_northwestRewriteStepCount
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

/-- Pullback-pushforward northeast rewrite-step count is counted by target and probe-target ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_northeastRewriteStepCount
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

/-- Pullback-pushforward southwest rewrite-step count is counted by source and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_southwestRewriteStepCount
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

/-- Pullback-pushforward southeast rewrite-step count is counted by target and probe-source ledgers. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_southeastRewriteStepCount
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
