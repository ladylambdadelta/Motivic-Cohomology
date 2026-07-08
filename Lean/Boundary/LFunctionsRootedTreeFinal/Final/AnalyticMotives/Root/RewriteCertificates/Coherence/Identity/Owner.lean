import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Coherence.Associativity.Owner

/-!
# Top-root identity coherence certificates

This file exposes the certificate ledgers attached to left- and right-identity
coherence cells under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a left-identity coherence cell. -/
def AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  TraceCoherenceCell.leftIdentityCertificateLedger source target

/-- The top-root left-identity coherence ledger records the compared paths and cell. -/
theorem AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.leftIdentity source target) ::
            ResidueChannelCertificateLedger.empty :=
  TraceCoherenceCell.leftIdentityCertificateLedger_eq_paths_cell
    source
    target

/-- The top-root left-identity coherence ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  TraceCoherenceCell.leftIdentityCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root left-identity coherence ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  TraceCoherenceCell.leftIdentityCertificateLedger_importedRectangles
    source
    target

/-- The top-root left-identity coherence rectangle count is the length of its payload. -/
theorem AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger
        source
        target).importedRectangles.length :=
  TraceCoherenceCell.leftIdentityCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root left-identity coherence ledger has source-path, target-path, and cell bookkeeping. -/
theorem AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  TraceCoherenceCell.leftIdentityCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root left-identity coherence ledger counts the compared source and target paths. -/
theorem AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.leftIdentityCoherenceCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCoherenceCell.leftIdentityCertificateLedger_rewriteStepCount
    source
    target

/-- The top root exposes the certificate ledger attached to a right-identity coherence cell. -/
def AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  TraceCoherenceCell.rightIdentityCertificateLedger source target

/-- The top-root right-identity coherence ledger records the compared paths and cell. -/
theorem AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.rightIdentity source target) ::
            ResidueChannelCertificateLedger.empty :=
  TraceCoherenceCell.rightIdentityCertificateLedger_eq_paths_cell
    source
    target

/-- The top-root right-identity coherence ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  TraceCoherenceCell.rightIdentityCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root right-identity coherence ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  TraceCoherenceCell.rightIdentityCertificateLedger_importedRectangles
    source
    target

/-- The top-root right-identity coherence rectangle count is the length of its payload. -/
theorem AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger
        source
        target).importedRectangles.length :=
  TraceCoherenceCell.rightIdentityCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root right-identity coherence ledger has source-path, target-path, and cell bookkeeping. -/
theorem AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  TraceCoherenceCell.rightIdentityCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root right-identity coherence ledger counts the compared source and target paths. -/
theorem AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.rightIdentityCoherenceCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCoherenceCell.rightIdentityCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
