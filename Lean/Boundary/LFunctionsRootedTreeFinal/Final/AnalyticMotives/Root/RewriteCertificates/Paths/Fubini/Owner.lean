import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Paths.WeightDrop.Owner

/-!
# Top-root Fubini rewrite-path certificates
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a Fubini path. -/
def AnalyticMotivesRoot.fubiniPathCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  TraceRewritePath.fubiniCertificateLedger source target

/-- The top-root Fubini path ledger is the singleton Fubini rewrite-path certificate. -/
theorem AnalyticMotivesRoot.fubiniPathCertificateLedger_eq_singleton
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.fubiniPathCertificateLedger source target =
      ResidueChannelCertificateLedger.singleton
        (ResidueChannelCertificateAtom.rewritePath
          (TraceRewritePath.fubini source target)) :=
  TraceRewritePath.fubiniCertificateLedger_eq_singleton
    source
    target

/-- The top-root Fubini path ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.fubiniPathCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.fubiniPathCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  TraceRewritePath.fubiniCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root Fubini path ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.fubiniPathCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.fubiniPathCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  TraceRewritePath.fubiniCertificateLedger_importedRectangles
    source
    target

/-- The top-root Fubini path rectangle count is the length of its rectangle payload. -/
theorem AnalyticMotivesRoot.fubiniPathCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.fubiniPathCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.fubiniPathCertificateLedger
        source
        target).importedRectangles.length :=
  TraceRewritePath.fubiniCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root Fubini path ledger has one trace-bookkeeping atom. -/
theorem AnalyticMotivesRoot.fubiniPathCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.fubiniPathCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.fubiniCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root Fubini path ledger counts one rewrite step. -/
theorem AnalyticMotivesRoot.fubiniPathCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.fubiniPathCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.fubiniCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
