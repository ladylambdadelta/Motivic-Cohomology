import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Certificates.Shape.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Certificates.Payload.Owner

/-!
# Top-root Stokes rewrite-path certificates
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a Stokes path. -/
def AnalyticMotivesRoot.stokesPathCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  TraceRewritePath.stokesCertificateLedger source target

/-- The top-root Stokes path ledger is the singleton Stokes rewrite-path certificate. -/
theorem AnalyticMotivesRoot.stokesPathCertificateLedger_eq_singleton
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.stokesPathCertificateLedger source target =
      ResidueChannelCertificateLedger.singleton
        (ResidueChannelCertificateAtom.rewritePath
          (TraceRewritePath.stokes source target)) :=
  TraceRewritePath.stokesCertificateLedger_eq_singleton
    source
    target

/-- The top-root Stokes path ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.stokesPathCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.stokesPathCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  TraceRewritePath.stokesCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root Stokes path ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.stokesPathCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.stokesPathCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  TraceRewritePath.stokesCertificateLedger_importedRectangles
    source
    target

/-- The top-root Stokes path rectangle count is the length of its rectangle payload. -/
theorem AnalyticMotivesRoot.stokesPathCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.stokesPathCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.stokesPathCertificateLedger
        source
        target).importedRectangles.length :=
  TraceRewritePath.stokesCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root Stokes path ledger has one trace-bookkeeping atom. -/
theorem AnalyticMotivesRoot.stokesPathCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.stokesPathCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  TraceRewritePath.stokesCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root Stokes path ledger counts one rewrite step. -/
theorem AnalyticMotivesRoot.stokesPathCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (AnalyticMotivesRoot.stokesPathCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  TraceRewritePath.stokesCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
