import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.Endpoint.LedgerCounts.Owner

/-!
# Motive-root endpoint ledger-count agreement under localized-arrow reassociation

This file exposes endpoint rectangle-list length and endpoint ledger-counter
agreement under reassociation through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: reassociation preserves endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointImportedRectangles_length_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles.length =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles.length :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointImportedRectangles_length_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint ledger imported-rectangle count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_importedRectangleCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint ledger trace-bookkeeping count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_traceBookkeepingCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint ledger rewrite-step count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_rewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
