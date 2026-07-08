import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Owner

/-!
# Endpoint payload of triple forward words

This file records whole-endpoint payload formulas for the two unstable
forward-word parenthesizations of a composable triple.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated triple forward word endpoint rectangles are first source then third target. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  rfl

/-- The right-associated triple forward word endpoint rectangles are first source then third target. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles =
      triple.first.sourceObject.importedRectangles ++
        triple.third.targetObject.importedRectangles :=
  rfl

/-- The left-associated triple forward word endpoint imported count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  rfl

/-- The right-associated triple forward word endpoint imported count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount +
        triple.third.targetObject.importedRectangleCount :=
  rfl

/-- The left-associated triple forward word endpoint ledger is first source then third target. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  rfl

/-- The right-associated triple forward word endpoint ledger is first source then third target. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger =
      ResidueChannelCertificateLedger.append
        triple.first.sourceObject.certificateLedger
        triple.third.targetObject.certificateLedger :=
  rfl

/-- The left-associated triple forward word endpoint bookkeeping count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  rfl

/-- The right-associated triple forward word endpoint bookkeeping count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount +
        triple.third.targetObject.traceBookkeepingCount :=
  rfl

/-- The left-associated triple forward word endpoint rewrite count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  rfl

/-- The right-associated triple forward word endpoint rewrite count is first source plus third target. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount +
        triple.third.targetObject.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
