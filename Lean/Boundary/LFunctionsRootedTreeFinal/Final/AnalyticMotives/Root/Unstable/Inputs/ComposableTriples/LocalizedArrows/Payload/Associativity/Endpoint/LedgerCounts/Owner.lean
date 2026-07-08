import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.Endpoint.LedgerCounts.Owner

/-!
# Public endpoint ledger-count agreement under localized-arrow reassociation

This file exposes endpoint rectangle-list length and endpoint ledger-counter
agreement under reassociation through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: reassociation preserves endpoint rectangle-list length. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_endpointImportedRectangles_length_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles.length =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles.length :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointImportedRectangles_length_eq
    triple

/-- Public wrapper: reassociation preserves endpoint ledger imported-rectangle count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_endpointCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointCertificateLedger_importedRectangleCount_eq
    triple

/-- Public wrapper: reassociation preserves endpoint ledger trace-bookkeeping count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_endpointCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointCertificateLedger_traceBookkeepingCount_eq
    triple

/-- Public wrapper: reassociation preserves endpoint ledger rewrite-step count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_endpointCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointCertificateLedger_rewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
