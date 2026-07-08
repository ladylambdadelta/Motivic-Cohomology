import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.Vertical.Owner

/-!
# Trace-calculus ledger counts for vertical payload operations

This file records certificate-ledger formulas for bookkeeping and rewrite-step
counts after vertical composition in the compact pullback-pushforward square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Vertical northwest bookkeeping count is counted by source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northwest_bookkeeping_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        (left ≫ right) =
      source.certificateLedger.traceBookkeepingCount +
        third.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_northwest_bookkeeping
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount_eq_certificateLedgers
      morphism
      right)

/-- Vertical northeast bookkeeping count is counted by target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northeast_bookkeeping_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        morphism
        (left ≫ right) =
      target.certificateLedger.traceBookkeepingCount +
        third.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_northeast_bookkeeping
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount_eq_certificateLedgers
      morphism
      right)

/-- Vertical southwest bookkeeping count is counted by source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southwest_bookkeeping_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        morphism
        (left ≫ right) =
      source.certificateLedger.traceBookkeepingCount +
        first.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_southwest_bookkeeping
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount_eq_certificateLedgers
      morphism
      left)

/-- Vertical southeast bookkeeping count is counted by target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southeast_bookkeeping_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        morphism
        (left ≫ right) =
      target.certificateLedger.traceBookkeepingCount +
        first.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_southeast_bookkeeping
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount_eq_certificateLedgers
      morphism
      left)

/-- Vertical northwest rewrite count is counted by source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northwest_rewrite_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        (left ≫ right) =
      source.certificateLedger.rewriteStepCount +
        third.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_northwest_rewrite
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.northwestRewriteStepCount_eq_certificateLedgers
      morphism
      right)

/-- Vertical northeast rewrite count is counted by target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_northeast_rewrite_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        morphism
        (left ≫ right) =
      target.certificateLedger.rewriteStepCount +
        third.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_northeast_rewrite
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.northeastRewriteStepCount_eq_certificateLedgers
      morphism
      right)

/-- Vertical southwest rewrite count is counted by source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southwest_rewrite_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        morphism
        (left ≫ right) =
      source.certificateLedger.rewriteStepCount +
        first.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_southwest_rewrite
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.southwestRewriteStepCount_eq_certificateLedgers
      morphism
      left)

/-- Vertical southeast rewrite count is counted by target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.verticalComp_southeast_rewrite_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        morphism
        (left ≫ right) =
      target.certificateLedger.rewriteStepCount +
        first.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.verticalComp_southeast_rewrite
      morphism
      left
      right)
    (TraceSixFunctorPullbackPushforward.southeastRewriteStepCount_eq_certificateLedgers
      morphism
      left)

end AnalyticMotives
end LFunctions
end Boundary
