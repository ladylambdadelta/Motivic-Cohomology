import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Paths.Residue.Owner

/-!
# Top-root channel rewrite-path certificates
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a channel path. -/
def AnalyticMotivesRoot.channelPathCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  TraceRewritePath.channelCertificateLedger source target

/-- The top-root channel path ledger is the singleton channel rewrite-path certificate. -/
theorem AnalyticMotivesRoot.channelPathCertificateLedger_eq_singleton
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.channelPathCertificateLedger source target =
      ResidueChannelCertificateLedger.singleton
        (ResidueChannelCertificateAtom.rewritePath
          (TraceRewritePath.channel source target)) :=
  TraceRewritePath.channelCertificateLedger_eq_singleton
    source
    target

/-- The top-root channel path ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.channelPathCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.channelPathCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  TraceRewritePath.channelCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root channel path ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.channelPathCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.channelPathCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  TraceRewritePath.channelCertificateLedger_importedRectangles
    source
    target

/-- The top-root channel path rectangle count is the length of its rectangle payload. -/
theorem AnalyticMotivesRoot.channelPathCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.channelPathCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.channelPathCertificateLedger
        source
        target).importedRectangles.length :=
  TraceRewritePath.channelCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root channel path ledger has one trace-bookkeeping atom. -/
theorem AnalyticMotivesRoot.channelPathCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.channelPathCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.channelCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root channel path ledger counts one rewrite step. -/
theorem AnalyticMotivesRoot.channelPathCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.channelPathCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.channelCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
