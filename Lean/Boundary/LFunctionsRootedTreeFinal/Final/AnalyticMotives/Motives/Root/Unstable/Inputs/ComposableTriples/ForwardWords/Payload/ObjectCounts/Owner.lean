import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.ObjectCounts.Owner

/-!
# Motive-root object-level counts of triple forward words

This file exposes object-level endpoint count facts for unstable forward-word
triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated source imported count is the first source count. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceImportedRectangleCount
    triple

/-- Motive-root wrapper: left-associated target imported count is the third target count. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetImportedRectangleCount
    triple

/-- Motive-root wrapper: right-associated source imported count is the first source count. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceImportedRectangleCount
    triple

/-- Motive-root wrapper: right-associated target imported count is the third target count. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetImportedRectangleCount
    triple

/-- Motive-root wrapper: left-associated source bookkeeping count is the first source count. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingObjectCount
    triple

/-- Motive-root wrapper: left-associated target bookkeeping count is the third target count. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetTraceBookkeepingObjectCount
    triple

/-- Motive-root wrapper: right-associated source bookkeeping count is the first source count. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingObjectCount
    triple

/-- Motive-root wrapper: right-associated target bookkeeping count is the third target count. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetTraceBookkeepingObjectCount
    triple

/-- Motive-root wrapper: left-associated source rewrite-step count is the first source count. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceRewriteStepObjectCount
    triple

/-- Motive-root wrapper: left-associated target rewrite-step count is the third target count. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetRewriteStepObjectCount
    triple

/-- Motive-root wrapper: right-associated source rewrite-step count is the first source count. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceRewriteStepObjectCount
    triple

/-- Motive-root wrapper: right-associated target rewrite-step count is the third target count. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetRewriteStepObjectCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
