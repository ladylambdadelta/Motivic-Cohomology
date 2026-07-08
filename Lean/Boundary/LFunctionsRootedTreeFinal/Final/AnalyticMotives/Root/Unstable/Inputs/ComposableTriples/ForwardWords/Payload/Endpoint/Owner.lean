import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Endpoint.Owner

/-!
# Public endpoint payload of triple forward words

This file exposes whole-endpoint payload formulas for unstable forward-word
triple composites through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated endpoint rectangles are first source then third target. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointImportedRectangles
    triple

/-- Public wrapper: right-associated endpoint rectangles are first source then third target. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointImportedRectangles
    triple

/-- Public wrapper: left-associated endpoint imported count is first source plus third target. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount
    triple

/-- Public wrapper: right-associated endpoint imported count is first source plus third target. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount
    triple

/-- Public wrapper: left-associated endpoint ledger is first source then third target. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointCertificateLedger
    triple

/-- Public wrapper: right-associated endpoint ledger is first source then third target. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointCertificateLedger
    triple

/-- Public wrapper: left-associated endpoint bookkeeping count is first source plus third target. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointTraceBookkeepingCount
    triple

/-- Public wrapper: right-associated endpoint bookkeeping count is first source plus third target. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointTraceBookkeepingCount
    triple

/-- Public wrapper: left-associated endpoint rewrite count is first source plus third target. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointRewriteStepCount
    triple

/-- Public wrapper: right-associated endpoint rewrite count is first source plus third target. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointRewriteStepCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
