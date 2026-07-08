import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.ByKind.Facts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.RewriteMaps.ByKind.Certificates.Owner

/-!
# Top-root by-kind rewrite certificates

This file exposes the one-step rewrite and trace-bookkeeping count facts for
the seven concrete analytic trace rewrite certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root records that a Stokes rewrite map carries one rewrite step. -/
theorem AnalyticMotivesRoot.stokesRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.stokesCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceAnalyticMotive.stokesRewriteMap_rewriteStepCount
    source
    target

/-- The top root records that a residue rewrite map carries one rewrite step. -/
theorem AnalyticMotivesRoot.residueRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.residueCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceAnalyticMotive.residueRewriteMap_rewriteStepCount
    source
    target

/-- The top root records that a channel rewrite map carries one rewrite step. -/
theorem AnalyticMotivesRoot.channelRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.channelCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceAnalyticMotive.channelRewriteMap_rewriteStepCount
    source
    target

/-- The top root records that a refinement rewrite map carries one rewrite step. -/
theorem AnalyticMotivesRoot.refinementRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.refinementCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceAnalyticMotive.refinementRewriteMap_rewriteStepCount
    source
    target

/-- The top root records that a schedule rewrite map carries one rewrite step. -/
theorem AnalyticMotivesRoot.scheduleRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.scheduleCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceAnalyticMotive.scheduleRewriteMap_rewriteStepCount
    source
    target

/-- The top root records that a weight-drop rewrite map carries one rewrite step. -/
theorem AnalyticMotivesRoot.weightDropRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDropCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceAnalyticMotive.weightDropRewriteMap_rewriteStepCount
    source
    target

/-- The top root records that a Fubini rewrite map carries one rewrite step. -/
theorem AnalyticMotivesRoot.fubiniRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.fubiniCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceAnalyticMotive.fubiniRewriteMap_rewriteStepCount
    source
    target

/-- The top root records that a Stokes rewrite map carries one bookkeeping atom. -/
theorem AnalyticMotivesRoot.stokesRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.stokesCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceAnalyticMotive.stokesRewriteMap_traceBookkeepingCount
    source
    target

/-- The top root records that a residue rewrite map carries one bookkeeping atom. -/
theorem AnalyticMotivesRoot.residueRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.residueCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceAnalyticMotive.residueRewriteMap_traceBookkeepingCount
    source
    target

/-- The top root records that a channel rewrite map carries one bookkeeping atom. -/
theorem AnalyticMotivesRoot.channelRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.channelCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceAnalyticMotive.channelRewriteMap_traceBookkeepingCount
    source
    target

/-- The top root records that a refinement rewrite map carries one bookkeeping atom. -/
theorem AnalyticMotivesRoot.refinementRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.refinementCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceAnalyticMotive.refinementRewriteMap_traceBookkeepingCount
    source
    target

/-- The top root records that a schedule rewrite map carries one bookkeeping atom. -/
theorem AnalyticMotivesRoot.scheduleRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.scheduleCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceAnalyticMotive.scheduleRewriteMap_traceBookkeepingCount
    source
    target

/-- The top root records that a weight-drop rewrite map carries one bookkeeping atom. -/
theorem AnalyticMotivesRoot.weightDropRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDropCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceAnalyticMotive.weightDropRewriteMap_traceBookkeepingCount
    source
    target

/-- The top root records that a Fubini rewrite map carries one bookkeeping atom. -/
theorem AnalyticMotivesRoot.fubiniRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.fubiniCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceAnalyticMotive.fubiniRewriteMap_traceBookkeepingCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
