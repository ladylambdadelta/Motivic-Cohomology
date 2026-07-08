import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoint.Owner

/-!
# Motive-root whole endpoint payload of localized-arrow triple composites

This file exposes whole-endpoint payload formulas for localized-forward-arrow
triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated endpoint rectangles are first source then third target. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointImportedRectangles
    triple

/-- Motive-root wrapper: right-associated endpoint rectangles are first source then third target. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointImportedRectangles
    triple

/-- Motive-root wrapper: left-associated endpoint imported count is first source plus third target. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount
    triple

/-- Motive-root wrapper: right-associated endpoint imported count is first source plus third target. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount
    triple

/-- Motive-root wrapper: left-associated endpoint ledger is first source then third target. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointCertificateLedger
    triple

/-- Motive-root wrapper: right-associated endpoint ledger is first source then third target. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointCertificateLedger
    triple

/-- Motive-root wrapper: left-associated endpoint bookkeeping count is first source plus third target. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount
    triple

/-- Motive-root wrapper: right-associated endpoint bookkeeping count is first source plus third target. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount
    triple

/-- Motive-root wrapper: left-associated endpoint rewrite count is first source plus third target. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointRewriteStepCount
    triple

/-- Motive-root wrapper: right-associated endpoint rewrite count is first source plus third target. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointRewriteStepCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
