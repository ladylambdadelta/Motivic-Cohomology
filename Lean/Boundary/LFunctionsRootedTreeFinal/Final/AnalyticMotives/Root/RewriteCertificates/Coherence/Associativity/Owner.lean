import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Coherence.Refinement.Owner

/-!
# Top-root associativity coherence certificate

This file exposes the certificate ledger attached to an associativity coherence
cell under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to an associativity coherence cell. -/
def AnalyticMotivesRoot.associativityCoherenceCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  TraceCoherenceCell.associativityCertificateLedger source target

/-- The top-root associativity coherence ledger records the compared paths and cell. -/
theorem AnalyticMotivesRoot.associativityCoherenceCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    AnalyticMotivesRoot.associativityCoherenceCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.associativity source target) ::
            ResidueChannelCertificateLedger.empty :=
  TraceCoherenceCell.associativityCertificateLedger_eq_paths_cell
    source
    target

/-- The top-root associativity coherence ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.associativityCoherenceCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.associativityCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  TraceCoherenceCell.associativityCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root associativity coherence ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.associativityCoherenceCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.associativityCoherenceCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  TraceCoherenceCell.associativityCertificateLedger_importedRectangles
    source
    target

/-- The top-root associativity coherence rectangle count is the length of its payload. -/
theorem AnalyticMotivesRoot.associativityCoherenceCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.associativityCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.associativityCoherenceCertificateLedger
        source
        target).importedRectangles.length :=
  TraceCoherenceCell.associativityCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root associativity coherence ledger has source-path, target-path, and cell bookkeeping. -/
theorem AnalyticMotivesRoot.associativityCoherenceCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.associativityCoherenceCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  TraceCoherenceCell.associativityCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root associativity coherence ledger counts the compared source and target paths. -/
theorem AnalyticMotivesRoot.associativityCoherenceCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.associativityCoherenceCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCoherenceCell.associativityCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
