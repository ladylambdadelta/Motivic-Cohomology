import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Counts.RewriteSteps.Owner

/-!
# Whole endpoint payload of localized-arrow triple composites

This file records whole-endpoint payload formulas for the two named
localized-forward-arrow parenthesizations of a composable triple.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated localized-arrow composite endpoint rectangles are first source then third target. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  rfl

/-- The right-associated localized-arrow composite endpoint rectangles are first source then third target. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  rfl

/-- The left-associated localized-arrow composite endpoint imported count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  rfl

/-- The right-associated localized-arrow composite endpoint imported count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  rfl

/-- The left-associated localized-arrow composite endpoint ledger is first source then third target. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  rfl

/-- The right-associated localized-arrow composite endpoint ledger is first source then third target. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  rfl

/-- The left-associated localized-arrow composite endpoint bookkeeping count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  rfl

/-- The right-associated localized-arrow composite endpoint bookkeeping count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  rfl

/-- The left-associated localized-arrow composite endpoint rewrite count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  rfl

/-- The right-associated localized-arrow composite endpoint rewrite count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
