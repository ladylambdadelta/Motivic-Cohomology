import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.ObjectCounts.Owner

/-!
# Public object-level counts of triple forward words

This file exposes object-level endpoint count facts for unstable forward-word
triple composites through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated source imported count is the first source count. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceImportedRectangleCount
    triple

/-- Public wrapper: left-associated target imported count is the third target count. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetImportedRectangleCount
    triple

/-- Public wrapper: right-associated source imported count is the first source count. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceImportedRectangleCount
    triple

/-- Public wrapper: right-associated target imported count is the third target count. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetImportedRectangleCount
    triple

/-- Public wrapper: left-associated source bookkeeping count is the first source count. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingObjectCount
    triple

/-- Public wrapper: left-associated target bookkeeping count is the third target count. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetTraceBookkeepingObjectCount
    triple

/-- Public wrapper: right-associated source bookkeeping count is the first source count. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingObjectCount
    triple

/-- Public wrapper: right-associated target bookkeeping count is the third target count. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetTraceBookkeepingObjectCount
    triple

/-- Public wrapper: left-associated source rewrite-step count is the first source count. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceRewriteStepObjectCount
    triple

/-- Public wrapper: left-associated target rewrite-step count is the third target count. -/
theorem AnalyticMotivesRoot.leftAssociatedUnstableForwardWord_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetRewriteStepObjectCount
    triple

/-- Public wrapper: right-associated source rewrite-step count is the first source count. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceRewriteStepObjectCount
    triple

/-- Public wrapper: right-associated target rewrite-step count is the third target count. -/
theorem AnalyticMotivesRoot.rightAssociatedUnstableForwardWord_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetRewriteStepObjectCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
