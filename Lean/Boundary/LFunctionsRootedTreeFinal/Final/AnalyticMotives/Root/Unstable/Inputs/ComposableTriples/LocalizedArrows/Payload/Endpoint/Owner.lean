import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoint.Owner

/-!
# Public whole endpoint payload of localized-arrow triple composites

This file exposes whole-endpoint payload formulas for localized-forward-arrow
triple composites through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated endpoint rectangles are first source then third target. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointImportedRectangles
    triple

/-- Public wrapper: right-associated endpoint rectangles are first source then third target. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointImportedRectangles
    triple

/-- Public wrapper: left-associated endpoint imported count is first source plus third target. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount
    triple

/-- Public wrapper: right-associated endpoint imported count is first source plus third target. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount
    triple

/-- Public wrapper: left-associated endpoint ledger is first source then third target. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointCertificateLedger
    triple

/-- Public wrapper: right-associated endpoint ledger is first source then third target. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointCertificateLedger
    triple

/-- Public wrapper: left-associated endpoint bookkeeping count is first source plus third target. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount
    triple

/-- Public wrapper: right-associated endpoint bookkeeping count is first source plus third target. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount
    triple

/-- Public wrapper: left-associated endpoint rewrite count is first source plus third target. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_endpointRewriteStepCount
    triple

/-- Public wrapper: right-associated endpoint rewrite count is first source plus third target. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_endpointRewriteStepCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
