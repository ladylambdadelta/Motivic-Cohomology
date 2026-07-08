import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Paths.Stokes.Owner

/-!
# Top-root residue rewrite-path certificates
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a residue path. -/
def AnalyticMotivesRoot.residuePathCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  TraceRewritePath.residueCertificateLedger source target

/-- The top-root residue path ledger is the singleton residue rewrite-path certificate. -/
theorem AnalyticMotivesRoot.residuePathCertificateLedger_eq_singleton
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.residuePathCertificateLedger source target =
      ResidueChannelCertificateLedger.singleton
        (ResidueChannelCertificateAtom.rewritePath
          (TraceRewritePath.residue source target)) :=
  TraceRewritePath.residueCertificateLedger_eq_singleton
    source
    target

/-- The top-root residue path ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.residuePathCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.residuePathCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  TraceRewritePath.residueCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root residue path ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.residuePathCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.residuePathCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  TraceRewritePath.residueCertificateLedger_importedRectangles
    source
    target

/-- The top-root residue path rectangle count is the length of its rectangle payload. -/
theorem AnalyticMotivesRoot.residuePathCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.residuePathCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.residuePathCertificateLedger
        source
        target).importedRectangles.length :=
  TraceRewritePath.residueCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root residue path ledger has one trace-bookkeeping atom. -/
theorem AnalyticMotivesRoot.residuePathCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.residuePathCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.residueCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root residue path ledger counts one rewrite step. -/
theorem AnalyticMotivesRoot.residuePathCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.residuePathCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.residueCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
