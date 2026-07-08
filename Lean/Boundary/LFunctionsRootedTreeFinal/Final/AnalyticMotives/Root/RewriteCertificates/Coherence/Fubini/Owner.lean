import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Certificates.Shape.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Certificates.Payload.Owner

/-!
# Top-root Fubini coherence certificate

This file exposes the certificate ledger attached to a Fubini coherence cell
under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a Fubini coherence cell. -/
def AnalyticMotivesRoot.fubiniCoherenceCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  TraceCoherenceCell.fubiniCertificateLedger source target

/-- The top-root Fubini coherence ledger records the compared paths and cell. -/
theorem AnalyticMotivesRoot.fubiniCoherenceCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    AnalyticMotivesRoot.fubiniCoherenceCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.fubini source target) ::
            ResidueChannelCertificateLedger.empty :=
  TraceCoherenceCell.fubiniCertificateLedger_eq_paths_cell
    source
    target

/-- The top-root Fubini coherence ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.fubiniCoherenceCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.fubiniCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  TraceCoherenceCell.fubiniCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root Fubini coherence ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.fubiniCoherenceCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.fubiniCoherenceCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  TraceCoherenceCell.fubiniCertificateLedger_importedRectangles
    source
    target

/-- The top-root Fubini coherence rectangle count is the length of its payload. -/
theorem AnalyticMotivesRoot.fubiniCoherenceCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.fubiniCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.fubiniCoherenceCertificateLedger
        source
        target).importedRectangles.length :=
  TraceCoherenceCell.fubiniCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root Fubini coherence ledger has source-path, target-path, and cell bookkeeping. -/
theorem AnalyticMotivesRoot.fubiniCoherenceCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.fubiniCoherenceCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  TraceCoherenceCell.fubiniCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root Fubini coherence ledger counts the compared source and target paths. -/
theorem AnalyticMotivesRoot.fubiniCoherenceCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.fubiniCoherenceCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCoherenceCell.fubiniCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
