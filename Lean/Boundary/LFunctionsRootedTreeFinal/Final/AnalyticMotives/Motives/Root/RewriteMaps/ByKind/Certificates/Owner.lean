import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.RewriteMaps.ByKind.Facts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Certificates.Payload.Owner

/-!
# Motive-root by-kind rewrite certificate counts

This file exposes the one-step and bookkeeping counts for primitive by-kind
rewrite certificate ledgers at the motive root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The motive root records that a Stokes rewrite map carries one rewrite step. -/
theorem TraceAnalyticMotive.stokesRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.stokesCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.stokesCertificateLedger_rewriteStepCount
    source
    target

/-- The motive root records that a residue rewrite map carries one rewrite step. -/
theorem TraceAnalyticMotive.residueRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.residueCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.residueCertificateLedger_rewriteStepCount
    source
    target

/-- The motive root records that a channel rewrite map carries one rewrite step. -/
theorem TraceAnalyticMotive.channelRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.channelCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.channelCertificateLedger_rewriteStepCount
    source
    target

/-- The motive root records that a refinement rewrite map carries one rewrite step. -/
theorem TraceAnalyticMotive.refinementRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.refinementCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.refinementCertificateLedger_rewriteStepCount
    source
    target

/-- The motive root records that a schedule rewrite map carries one rewrite step. -/
theorem TraceAnalyticMotive.scheduleRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.scheduleCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.scheduleCertificateLedger_rewriteStepCount
    source
    target

/-- The motive root records that a weight-drop rewrite map carries one rewrite step. -/
theorem TraceAnalyticMotive.weightDropRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDropCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.weightDropCertificateLedger_rewriteStepCount
    source
    target

/-- The motive root records that a Fubini rewrite map carries one rewrite step. -/
theorem TraceAnalyticMotive.fubiniRewriteMap_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.fubiniCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.fubiniCertificateLedger_rewriteStepCount
    source
    target

/-- The motive root records that a Stokes rewrite map carries one bookkeeping atom. -/
theorem TraceAnalyticMotive.stokesRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.stokesCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.stokesCertificateLedger_traceBookkeepingCount
    source
    target

/-- The motive root records that a residue rewrite map carries one bookkeeping atom. -/
theorem TraceAnalyticMotive.residueRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.residueCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.residueCertificateLedger_traceBookkeepingCount
    source
    target

/-- The motive root records that a channel rewrite map carries one bookkeeping atom. -/
theorem TraceAnalyticMotive.channelRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.channelCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.channelCertificateLedger_traceBookkeepingCount
    source
    target

/-- The motive root records that a refinement rewrite map carries one bookkeeping atom. -/
theorem TraceAnalyticMotive.refinementRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.refinementCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.refinementCertificateLedger_traceBookkeepingCount
    source
    target

/-- The motive root records that a schedule rewrite map carries one bookkeeping atom. -/
theorem TraceAnalyticMotive.scheduleRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.scheduleCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.scheduleCertificateLedger_traceBookkeepingCount
    source
    target

/-- The motive root records that a weight-drop rewrite map carries one bookkeeping atom. -/
theorem TraceAnalyticMotive.weightDropRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDropCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.weightDropCertificateLedger_traceBookkeepingCount
    source
    target

/-- The motive root records that a Fubini rewrite map carries one bookkeeping atom. -/
theorem TraceAnalyticMotive.fubiniRewriteMap_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.fubiniCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.fubiniCertificateLedger_traceBookkeepingCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
