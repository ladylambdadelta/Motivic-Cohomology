import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Coherence.StokesResidue.Owner

/-!
# Top-root refinement coherence certificate

This file exposes the certificate ledger attached to a refinement coherence
cell under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a refinement coherence cell. -/
def AnalyticMotivesRoot.refinementCoherenceCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  TraceCoherenceCell.refinementCertificateLedger source target

/-- The top-root refinement coherence ledger records the compared paths and cell. -/
theorem AnalyticMotivesRoot.refinementCoherenceCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    AnalyticMotivesRoot.refinementCoherenceCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.refinement source target) ::
            ResidueChannelCertificateLedger.empty :=
  TraceCoherenceCell.refinementCertificateLedger_eq_paths_cell
    source
    target

/-- The top-root refinement coherence ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.refinementCoherenceCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.refinementCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  TraceCoherenceCell.refinementCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root refinement coherence ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.refinementCoherenceCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.refinementCoherenceCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  TraceCoherenceCell.refinementCertificateLedger_importedRectangles
    source
    target

/-- The top-root refinement coherence rectangle count is the length of its payload. -/
theorem AnalyticMotivesRoot.refinementCoherenceCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.refinementCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.refinementCoherenceCertificateLedger
        source
        target).importedRectangles.length :=
  TraceCoherenceCell.refinementCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root refinement coherence ledger has source-path, target-path, and cell bookkeeping. -/
theorem AnalyticMotivesRoot.refinementCoherenceCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.refinementCoherenceCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  TraceCoherenceCell.refinementCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root refinement coherence ledger counts the compared source and target paths. -/
theorem AnalyticMotivesRoot.refinementCoherenceCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.refinementCoherenceCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCoherenceCell.refinementCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
