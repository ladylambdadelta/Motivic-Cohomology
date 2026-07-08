import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoint.LedgerCounts.Owner

/-!
# Public endpoint ledger-count facts for localized-arrow triple composites

This file exposes endpoint length and ledger-count facts for localized-forward-arrow
triple composites through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated endpoint imported count is the endpoint-list length. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles.length :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_length
    triple

/-- Public wrapper: right-associated endpoint imported count is the endpoint-list length. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles.length :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_length
    triple

/-- Public wrapper: left-associated endpoint imported count is counted by the ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated endpoint imported count is counted by the ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    triple

/-- Public wrapper: left-associated endpoint bookkeeping count is counted by the ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated endpoint bookkeeping count is counted by the ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple

/-- Public wrapper: left-associated endpoint rewrite count is counted by the ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated endpoint rewrite count is counted by the ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    triple

end AnalyticMotives
end LFunctions
end Boundary
