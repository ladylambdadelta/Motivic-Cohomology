import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Coherence.ResidueChannel.Owner

/-!
# Top-root Stokes-residue coherence certificate

This file exposes the certificate ledger attached to a Stokes-residue coherence
cell under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a Stokes-residue cell. -/
def AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  TraceCoherenceCell.stokesResidueCertificateLedger source target

/-- The top-root Stokes-residue ledger records the compared paths and cell. -/
theorem AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.stokesResidue source target) ::
            ResidueChannelCertificateLedger.empty :=
  TraceCoherenceCell.stokesResidueCertificateLedger_eq_paths_cell
    source
    target

/-- The top-root Stokes-residue ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  TraceCoherenceCell.stokesResidueCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root Stokes-residue ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  TraceCoherenceCell.stokesResidueCertificateLedger_importedRectangles
    source
    target

/-- The top-root Stokes-residue rectangle count is the length of its payload. -/
theorem AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger
        source
        target).importedRectangles.length :=
  TraceCoherenceCell.stokesResidueCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root Stokes-residue ledger has source-path, target-path, and cell bookkeeping. -/
theorem AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  TraceCoherenceCell.stokesResidueCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root Stokes-residue ledger counts the compared source and target paths. -/
theorem AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.stokesResidueCoherenceCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCoherenceCell.stokesResidueCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
