import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Endpoint.Owner

/-!
# Motive-root endpoint payload of triple forward words

This file exposes whole-endpoint payload formulas for unstable forward-word
triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated endpoint rectangles are first source then third target. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointImportedRectangles
    triple

/-- Motive-root wrapper: right-associated endpoint rectangles are first source then third target. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointImportedRectangles
    triple

/-- Motive-root wrapper: left-associated endpoint imported count is first source plus third target. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount
    triple

/-- Motive-root wrapper: right-associated endpoint imported count is first source plus third target. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount
    triple

/-- Motive-root wrapper: left-associated endpoint ledger is first source then third target. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointCertificateLedger
    triple

/-- Motive-root wrapper: right-associated endpoint ledger is first source then third target. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointCertificateLedger
    triple

/-- Motive-root wrapper: left-associated endpoint bookkeeping count is first source plus third target. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointTraceBookkeepingCount
    triple

/-- Motive-root wrapper: right-associated endpoint bookkeeping count is first source plus third target. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointTraceBookkeepingCount
    triple

/-- Motive-root wrapper: left-associated endpoint rewrite count is first source plus third target. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointRewriteStepCount
    triple

/-- Motive-root wrapper: right-associated endpoint rewrite count is first source plus third target. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointRewriteStepCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
