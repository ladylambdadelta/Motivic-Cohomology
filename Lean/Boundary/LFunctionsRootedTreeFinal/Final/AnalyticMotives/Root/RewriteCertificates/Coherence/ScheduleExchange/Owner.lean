import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteCertificates.Coherence.Fubini.Owner

/-!
# Top-root schedule-exchange coherence certificate

This file exposes the certificate ledger attached to a schedule-exchange
coherence cell under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger attached to a schedule-exchange cell. -/
def AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger
    (source target : TraceRewritePath) :
    ResidueChannelCertificateLedger :=
  TraceCoherenceCell.scheduleExchangeCertificateLedger source target

/-- The top-root schedule-exchange ledger records the compared paths and cell. -/
theorem AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger_eq_paths_cell
    (source target : TraceRewritePath) :
    AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger source target =
      ResidueChannelCertificateAtom.rewritePath source ::
        ResidueChannelCertificateAtom.rewritePath target ::
          ResidueChannelCertificateAtom.coherenceCell
              (TraceCoherenceCell.scheduleExchange source target) ::
            ResidueChannelCertificateLedger.empty :=
  TraceCoherenceCell.scheduleExchangeCertificateLedger_eq_paths_cell
    source
    target

/-- The top-root schedule-exchange ledger has no imported finite rectangles. -/
theorem AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger_importedRectangleCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      0 + (0 + (0 + 0)) :=
  TraceCoherenceCell.scheduleExchangeCertificateLedger_importedRectangleCount
    source
    target

/-- The top-root schedule-exchange ledger exposes an empty rectangle payload. -/
theorem AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger_importedRectangles
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger
      source
      target).importedRectangles =
      [] ++ ([] ++ ([] ++ [])) :=
  TraceCoherenceCell.scheduleExchangeCertificateLedger_importedRectangles
    source
    target

/-- The top-root schedule-exchange rectangle count is the length of its payload. -/
theorem AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger_importedRectangleCount_eq_length
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger
      source
      target).importedRectangleCount =
      (AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger
        source
        target).importedRectangles.length :=
  TraceCoherenceCell.scheduleExchangeCertificateLedger_importedRectangleCount_eq_length
    source
    target

/-- The top-root schedule-exchange ledger has source-path, target-path, and cell bookkeeping. -/
theorem AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger_traceBookkeepingCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + (1 + (1 + 0)) :=
  TraceCoherenceCell.scheduleExchangeCertificateLedger_traceBookkeepingCount
    source
    target

/-- The top-root schedule-exchange ledger counts the compared source and target paths. -/
theorem AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger_rewriteStepCount
    (source target : TraceRewritePath) :
    (AnalyticMotivesRoot.scheduleExchangeCoherenceCertificateLedger
      source
      target).rewriteStepCount =
      source.stepCount + (target.stepCount + (0 + 0)) :=
  TraceCoherenceCell.scheduleExchangeCertificateLedger_rewriteStepCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
