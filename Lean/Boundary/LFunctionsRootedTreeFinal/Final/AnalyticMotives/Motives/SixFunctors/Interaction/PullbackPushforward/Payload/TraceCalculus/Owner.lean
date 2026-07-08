import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.LedgerCounts.Owner

/-!
# Trace-calculus counts for the compact pullback-pushforward square

This file records the bookkeeping and rewrite-step payloads carried by the
four corners of the concrete compact-generator pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Northwest corner trace-bookkeeping count in the pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount
    probe

/-- Northeast corner trace-bookkeeping count in the pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount
    probe

/-- Southwest corner trace-bookkeeping count in the pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount
    probe

/-- Southeast corner trace-bookkeeping count in the pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount
    probe

/-- Northwest corner rewrite-step count in the pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount
    probe

/-- Northeast corner rewrite-step count in the pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount
    probe

/-- Southwest corner rewrite-step count in the pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount
    probe

/-- Southeast corner rewrite-step count in the pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount
    probe

/-- Northwest bookkeeping count is counted by source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        probe =
      source.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount_eq_source_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount_eq_target_certificateLedger
      probe)

/-- Northeast bookkeeping count is counted by target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        probe =
      target.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount_eq_target_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount_eq_target_certificateLedger
      probe)

/-- Southwest bookkeeping count is counted by source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        probe =
      source.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount_eq_source_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount_eq_source_certificateLedger
      probe)

/-- Southeast bookkeeping count is counted by target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        probe =
      target.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount_eq_target_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount_eq_source_certificateLedger
      probe)

/-- Northwest rewrite-step count is counted by source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.northwestRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        probe =
      source.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount_eq_source_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount_eq_target_certificateLedger
      probe)

/-- Northeast rewrite-step count is counted by target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.northeastRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        probe =
      target.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount_eq_target_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount_eq_target_certificateLedger
      probe)

/-- Southwest rewrite-step count is counted by source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.southwestRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        probe =
      source.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount_eq_source_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount_eq_source_certificateLedger
      probe)

/-- Southeast rewrite-step count is counted by target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.southeastRewriteStepCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        probe =
      target.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount_eq_target_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount_eq_source_certificateLedger
      probe)

end AnalyticMotives
end LFunctions
end Boundary
