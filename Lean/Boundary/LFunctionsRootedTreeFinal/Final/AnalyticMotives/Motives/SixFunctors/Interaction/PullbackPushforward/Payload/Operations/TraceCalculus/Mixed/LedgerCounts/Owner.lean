import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.TraceCalculus.Mixed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.TraceCalculus.Owner

/-!
# Trace-calculus ledger counts for mixed pullback-pushforward operations

This file records certificate-ledger formulas for bookkeeping and rewrite-step
counts after simultaneous horizontal and vertical composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mixed northwest bookkeeping count is counted by left source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northwest_bookkeeping_eq_certificateLedgers
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.traceBookkeepingCount +
        vThird.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_northwest_bookkeeping
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount_eq_certificateLedgers
      hLeft
      vRight)

/-- Mixed northeast bookkeeping count is counted by right target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northeast_bookkeeping_eq_certificateLedgers
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.traceBookkeepingCount +
        vThird.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_northeast_bookkeeping
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.northeastTraceBookkeepingCount_eq_certificateLedgers
      hRight
      vRight)

/-- Mixed southwest bookkeeping count is counted by left source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southwest_bookkeeping_eq_certificateLedgers
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.traceBookkeepingCount +
        vFirst.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_southwest_bookkeeping
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.southwestTraceBookkeepingCount_eq_certificateLedgers
      hLeft
      vLeft)

/-- Mixed southeast bookkeeping count is counted by right target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southeast_bookkeeping_eq_certificateLedgers
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.traceBookkeepingCount +
        vFirst.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_southeast_bookkeeping
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.southeastTraceBookkeepingCount_eq_certificateLedgers
      hRight
      vLeft)

/-- Mixed northwest rewrite count is counted by left source and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northwest_rewrite_eq_certificateLedgers
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.rewriteStepCount +
        vThird.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_northwest_rewrite
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.northwestRewriteStepCount_eq_certificateLedgers
      hLeft
      vRight)

/-- Mixed northeast rewrite count is counted by right target and right probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_northeast_rewrite_eq_certificateLedgers
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northeastRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.rewriteStepCount +
        vThird.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_northeast_rewrite
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.northeastRewriteStepCount_eq_certificateLedgers
      hRight
      vRight)

/-- Mixed southwest rewrite count is counted by left source and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southwest_rewrite_eq_certificateLedgers
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southwestRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.rewriteStepCount +
        vFirst.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_southwest_rewrite
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.southwestRewriteStepCount_eq_certificateLedgers
      hLeft
      vLeft)

/-- Mixed southeast rewrite count is counted by right target and left probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.mixedComp_southeast_rewrite_eq_certificateLedgers
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.southeastRewriteStepCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hThird.certificateLedger.rewriteStepCount +
        vFirst.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceSixFunctorPullbackPushforward.mixedComp_southeast_rewrite
      hLeft
      hRight
      vLeft
      vRight)
    (TraceSixFunctorPullbackPushforward.southeastRewriteStepCount_eq_certificateLedgers
      hRight
      vLeft)

end AnalyticMotives
end LFunctions
end Boundary
