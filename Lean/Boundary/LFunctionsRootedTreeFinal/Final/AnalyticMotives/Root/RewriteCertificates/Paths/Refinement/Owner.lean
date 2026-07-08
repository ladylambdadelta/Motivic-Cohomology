import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Paths.Channel.Owner

/-!
# Top-root refinement rewrite-path certificates
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a refinement path. -/
def AnalyticMotivesRoot.refinementPathCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  TraceRewritePath.refinementCertificateLedger source target

/-- The top-root refinement path ledger is the singleton refinement rewrite-path certificate. -/
theorem AnalyticMotivesRoot.refinementPathCertificateLedger_eq_singleton
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.refinementPathCertificateLedger source target =
      ResidueChannelCertificateLedger.singleton
        (ResidueChannelCertificateAtom.rewritePath
          (TraceRewritePath.refinement source target)) :=
  TraceRewritePath.refinementCertificateLedger_eq_singleton
    source
    target

/-- The top-root refinement path ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.refinementPathCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.refinementPathCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  TraceRewritePath.refinementCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root refinement path ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.refinementPathCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.refinementPathCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  TraceRewritePath.refinementCertificateLedger_importedRectangles
    source
    target

/-- The top-root refinement path rectangle count is the length of its rectangle payload. -/
theorem AnalyticMotivesRoot.refinementPathCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.refinementPathCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.refinementPathCertificateLedger
        source
        target).importedRectangles.length :=
  TraceRewritePath.refinementCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root refinement path ledger has one trace-bookkeeping atom. -/
theorem AnalyticMotivesRoot.refinementPathCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.refinementPathCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.refinementCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root refinement path ledger counts one rewrite step. -/
theorem AnalyticMotivesRoot.refinementPathCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.refinementPathCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.refinementCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
