import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Payload.TraceCalculus.Owner

/-!
# Top-root pullback-pushforward square trace-calculus payload

This file mirrors the motive-root four-corner trace-bookkeeping and
rewrite-step count formulas under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root northwest trace-bookkeeping count wrapper. -/
theorem AnalyticMotivesRoot.publicNorthwestTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        probe =
      source.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicNorthwestTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Top-root northeast trace-bookkeeping count wrapper. -/
theorem AnalyticMotivesRoot.publicNortheastTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        probe =
      target.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicNortheastTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Top-root southwest trace-bookkeeping count wrapper. -/
theorem AnalyticMotivesRoot.publicSouthwestTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        probe =
      source.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicSouthwestTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Top-root southeast trace-bookkeeping count wrapper. -/
theorem AnalyticMotivesRoot.publicSoutheastTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        probe =
      target.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicSoutheastTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Top-root northwest rewrite-step count wrapper. -/
theorem AnalyticMotivesRoot.publicNorthwestRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        probe =
      source.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicNorthwestRewriteStepCount_eq_certificateLedgers
    morphism
    probe

/-- Top-root northeast rewrite-step count wrapper. -/
theorem AnalyticMotivesRoot.publicNortheastRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        probe =
      target.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicNortheastRewriteStepCount_eq_certificateLedgers
    morphism
    probe

/-- Top-root southwest rewrite-step count wrapper. -/
theorem AnalyticMotivesRoot.publicSouthwestRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        probe =
      source.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicSouthwestRewriteStepCount_eq_certificateLedgers
    morphism
    probe

/-- Top-root southeast rewrite-step count wrapper. -/
theorem AnalyticMotivesRoot.publicSoutheastRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        probe =
      target.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicSoutheastRewriteStepCount_eq_certificateLedgers
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
