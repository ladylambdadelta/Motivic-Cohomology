import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Paths.Schedule.Owner

/-!
# Top-root weight-drop rewrite-path certificates
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a weight-drop path. -/
def AnalyticMotivesRoot.weightDropPathCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  TraceRewritePath.weightDropCertificateLedger source target

/-- The top-root weight-drop path ledger is the singleton weight-drop rewrite-path certificate. -/
theorem AnalyticMotivesRoot.weightDropPathCertificateLedger_eq_singleton
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.weightDropPathCertificateLedger source target =
      ResidueChannelCertificateLedger.singleton
        (ResidueChannelCertificateAtom.rewritePath
          (TraceRewritePath.weightDrop source target)) :=
  TraceRewritePath.weightDropCertificateLedger_eq_singleton
    source
    target

/-- The top-root weight-drop path ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.weightDropPathCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.weightDropPathCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  TraceRewritePath.weightDropCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root weight-drop path ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.weightDropPathCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.weightDropPathCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  TraceRewritePath.weightDropCertificateLedger_importedRectangles
    source
    target

/-- The top-root weight-drop path rectangle count is the length of its rectangle payload. -/
theorem AnalyticMotivesRoot.weightDropPathCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.weightDropPathCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.weightDropPathCertificateLedger
        source
        target).importedRectangles.length :=
  TraceRewritePath.weightDropCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root weight-drop path ledger has one trace-bookkeeping atom. -/
theorem AnalyticMotivesRoot.weightDropPathCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.weightDropPathCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.weightDropCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root weight-drop path ledger counts one rewrite step. -/
theorem AnalyticMotivesRoot.weightDropPathCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.weightDropPathCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.weightDropCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
