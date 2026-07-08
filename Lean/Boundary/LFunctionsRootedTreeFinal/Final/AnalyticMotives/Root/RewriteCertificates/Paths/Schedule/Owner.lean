import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Paths.Refinement.Owner

/-!
# Top-root schedule rewrite-path certificates
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a schedule path. -/
def AnalyticMotivesRoot.schedulePathCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  TraceRewritePath.scheduleCertificateLedger source target

/-- The top-root schedule path ledger is the singleton schedule rewrite-path certificate. -/
theorem AnalyticMotivesRoot.schedulePathCertificateLedger_eq_singleton
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.schedulePathCertificateLedger source target =
      ResidueChannelCertificateLedger.singleton
        (ResidueChannelCertificateAtom.rewritePath
          (TraceRewritePath.schedule source target)) :=
  TraceRewritePath.scheduleCertificateLedger_eq_singleton
    source
    target

/-- The top-root schedule path ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.schedulePathCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.schedulePathCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  TraceRewritePath.scheduleCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root schedule path ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.schedulePathCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.schedulePathCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  TraceRewritePath.scheduleCertificateLedger_importedRectangles
    source
    target

/-- The top-root schedule path rectangle count is the length of its rectangle payload. -/
theorem AnalyticMotivesRoot.schedulePathCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.schedulePathCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.schedulePathCertificateLedger
        source
        target).importedRectangles.length :=
  TraceRewritePath.scheduleCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root schedule path ledger has one trace-bookkeeping atom. -/
theorem AnalyticMotivesRoot.schedulePathCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.schedulePathCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.scheduleCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root schedule path ledger counts one rewrite step. -/
theorem AnalyticMotivesRoot.schedulePathCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.schedulePathCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.scheduleCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
