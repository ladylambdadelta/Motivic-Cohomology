import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Coherence.ScheduleExchange.Owner

/-!
# Top-root residue-channel coherence certificate

This file exposes the certificate ledger attached to a residue-channel
coherence cell under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a residue-channel cell. -/
def AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  TraceCoherenceCell.residueChannelCertificateLedger source target

/-- The top-root residue-channel ledger records the compared paths and cell. -/
theorem AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.residueChannel source target) ::
            ResidueChannelCertificateLedger.empty :=
  TraceCoherenceCell.residueChannelCertificateLedger_eq_paths_cell
    source
    target

/-- The top-root residue-channel ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  TraceCoherenceCell.residueChannelCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root residue-channel ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  TraceCoherenceCell.residueChannelCertificateLedger_importedRectangles
    source
    target

/-- The top-root residue-channel rectangle count is the length of its payload. -/
theorem AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger
        source
        target).importedRectangles.length :=
  TraceCoherenceCell.residueChannelCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root residue-channel ledger has source-path, target-path, and cell bookkeeping. -/
theorem AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  TraceCoherenceCell.residueChannelCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root residue-channel ledger counts the compared source and target paths. -/
theorem AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.residueChannelCoherenceCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCoherenceCell.residueChannelCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
