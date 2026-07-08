import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.Endpoint.Owner

/-!
# Endpoint ledger-count agreement under localized-arrow reassociation

This file records that reassociation preserves the endpoint rectangle-list
length and endpoint ledger counters of named localized-forward-arrow triple
composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Reassociation preserves endpoint rectangle-list length for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointImportedRectangles_length_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles.length =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles.length :=
  congrArg
    List.length
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointImportedRectangles_eq
      triple)

/-- Reassociation preserves endpoint ledger imported-rectangle count. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_eq
      triple)

/-- Reassociation preserves endpoint ledger trace-bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_eq
      triple)

/-- Reassociation preserves endpoint ledger rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_eq
      triple)

end AnalyticMotives
end LFunctions
end Boundary
