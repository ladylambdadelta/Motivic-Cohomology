import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Endpoint.LedgerCounts.Owner

/-!
# Public endpoint ledger-count facts for triple forward words

This file exposes endpoint length and ledger-count facts for unstable
forward-word triple composites through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated endpoint imported count is the endpoint-list length. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles.length :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_length
    triple

/-- Public wrapper: right-associated endpoint imported count is the endpoint-list length. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles.length :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_length
    triple

/-- Public wrapper: left-associated endpoint imported count is counted by the ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated endpoint imported count is counted by the ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_certificateLedger_count
    triple

/-- Public wrapper: left-associated endpoint bookkeeping count is counted by the ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated endpoint bookkeeping count is counted by the ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple

/-- Public wrapper: left-associated endpoint rewrite count is counted by the ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointRewriteStepCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated endpoint rewrite count is counted by the ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointRewriteStepCount_eq_certificateLedger_count
    triple

end AnalyticMotives
end LFunctions
end Boundary
