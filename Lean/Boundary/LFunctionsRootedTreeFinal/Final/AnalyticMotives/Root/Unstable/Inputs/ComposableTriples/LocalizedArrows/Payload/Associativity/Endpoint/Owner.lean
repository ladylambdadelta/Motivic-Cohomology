import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.Endpoint.Owner

/-!
# Public whole-endpoint agreement under localized-arrow reassociation

This file exposes whole-endpoint payload agreement for reassociation of named
localized-forward-arrow triple composites through the public analytic-motives
root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: reassociation preserves endpoint imported rectangles. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_endpointImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointImportedRectangles_eq
    triple

/-- Public wrapper: reassociation preserves endpoint imported-rectangle count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_endpointImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointImportedRectangleCount_eq
    triple

/-- Public wrapper: reassociation preserves endpoint certificate ledger. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_endpointCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointCertificateLedger_eq
    triple

/-- Public wrapper: reassociation preserves endpoint trace-bookkeeping count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq
    triple

/-- Public wrapper: reassociation preserves endpoint rewrite-step count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_endpointRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointRewriteStepCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_endpointRewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
