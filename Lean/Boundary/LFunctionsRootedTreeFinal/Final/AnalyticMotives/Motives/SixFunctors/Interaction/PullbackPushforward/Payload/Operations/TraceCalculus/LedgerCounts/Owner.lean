import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.Owner

/-!
# Trace-calculus ledger counts for horizontal payload operations

This file records certificate-ledger formulas for bookkeeping and rewrite-step
counts after horizontal composition in the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Horizontal northwest bookkeeping count is counted by the left source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northwest_bookkeeping_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (left ≫ right)
        probe =
      first.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northwest_bookkeeping
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount_eq_certificateLedgers
      left
      probe)

/-- Horizontal northeast bookkeeping count is counted by the right target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northeast_bookkeeping_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (left ≫ right)
        probe =
      third.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northeast_bookkeeping
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount_eq_certificateLedgers
      right
      probe)

/-- Horizontal southwest bookkeeping count is counted by the left source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southwest_bookkeeping_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (left ≫ right)
        probe =
      first.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southwest_bookkeeping
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount_eq_certificateLedgers
      left
      probe)

/-- Horizontal southeast bookkeeping count is counted by the right target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southeast_bookkeeping_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (left ≫ right)
        probe =
      third.certificateLedger.traceBookkeepingCount +
        probeSource.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southeast_bookkeeping
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount_eq_certificateLedgers
      right
      probe)

/-- Horizontal northwest rewrite count is counted by the left source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rewrite_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (left ≫ right)
        probe =
      first.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northwest_rewrite
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.northwestRewriteStepCount_eq_certificateLedgers
      left
      probe)

/-- Horizontal northeast rewrite count is counted by the right target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rewrite_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (left ≫ right)
        probe =
      third.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_northeast_rewrite
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.northeastRewriteStepCount_eq_certificateLedgers
      right
      probe)

/-- Horizontal southwest rewrite count is counted by the left source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rewrite_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (left ≫ right)
        probe =
      first.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southwest_rewrite
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.southwestRewriteStepCount_eq_certificateLedgers
      left
      probe)

/-- Horizontal southeast rewrite count is counted by the right target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rewrite_eq_certificateLedgers
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (left ≫ right)
        probe =
      third.certificateLedger.rewriteStepCount +
        probeSource.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.horizontalComp_southeast_rewrite
      left
      right
      probe)
    (TraceSixFunctorPullbackPushforward.southeastRewriteStepCount_eq_certificateLedgers
      right
      probe)

end AnalyticMotives
end LFunctions
end Boundary
