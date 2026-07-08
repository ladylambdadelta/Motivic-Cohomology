import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.Owner

/-!
# Whole-endpoint agreement under localized-arrow triple reassociation

This file records whole-endpoint payload agreement for reassociation of named
localized-forward-arrow triple composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Reassociation preserves endpoint imported rectangles for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointImportedRectangles_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles :=
  congrArg
    TraceLocalizationWordClass.endpointImportedRectangles
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves endpoint imported-rectangle count for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointImportedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount :=
  congrArg
    TraceLocalizationWordClass.endpointImportedRectangleCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves endpoint certificate ledger for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointCertificateLedger_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger :=
  congrArg
    TraceLocalizationWordClass.endpointCertificateLedger
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves endpoint trace-bookkeeping count for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount :=
  congrArg
    TraceLocalizationWordClass.endpointTraceBookkeepingCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

/-- Reassociation preserves endpoint rewrite-step count for named localized-arrow composites. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_endpointRewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointRewriteStepCount :=
  congrArg
    TraceLocalizationWordClass.endpointRewriteStepCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
      triple)

end AnalyticMotives
end LFunctions
end Boundary
