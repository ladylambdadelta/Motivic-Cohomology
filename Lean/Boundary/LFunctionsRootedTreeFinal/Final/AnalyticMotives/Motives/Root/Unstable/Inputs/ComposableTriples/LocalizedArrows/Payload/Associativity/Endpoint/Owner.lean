import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.Endpoint.Owner

/-!
# Motive-root whole-endpoint agreement under localized-arrow reassociation

This file exposes whole-endpoint payload agreement for reassociation of named
localized-forward-arrow triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: reassociation preserves endpoint imported rectangles. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointImportedRectangles_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint imported-rectangle count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointImportedRectangleCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint certificate ledger. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint trace-bookkeeping count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint rewrite-step count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointRewriteStepCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointRewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
