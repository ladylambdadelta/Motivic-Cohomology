import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoint.LedgerCounts.Owner

/-!
# Motive-root endpoint ledger-count facts for localized-arrow triple composites

This file exposes endpoint length and ledger-count facts for localized-forward-arrow
triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated endpoint imported count is the endpoint-list length. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles.length :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_length
    triple

/-- Motive-root wrapper: right-associated endpoint imported count is the endpoint-list length. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles.length :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_length
    triple

/-- Motive-root wrapper: left-associated endpoint imported count is counted by the ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated endpoint imported count is counted by the ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: left-associated endpoint bookkeeping count is counted by the ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated endpoint bookkeeping count is counted by the ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: left-associated endpoint rewrite count is counted by the ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated endpoint rewrite count is counted by the ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    triple

end AnalyticMotives
end LFunctions
end Boundary
