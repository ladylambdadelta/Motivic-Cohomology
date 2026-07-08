import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.ObjectCounts.Owner

/-!
# Motive-root object-level counts of localized-arrow triple composites

This file exposes object-level endpoint count facts for localized-forward-arrow
triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated source imported count is the first source count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
    triple

/-- Motive-root wrapper: left-associated target imported count is the third target count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
    triple

/-- Motive-root wrapper: right-associated source imported count is the first source count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
    triple

/-- Motive-root wrapper: right-associated target imported count is the third target count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
    triple

/-- Motive-root wrapper: left-associated source bookkeeping count is the first source count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
    triple

/-- Motive-root wrapper: left-associated target bookkeeping count is the third target count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
    triple

/-- Motive-root wrapper: right-associated source bookkeeping count is the first source count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
    triple

/-- Motive-root wrapper: right-associated target bookkeeping count is the third target count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
    triple

/-- Motive-root wrapper: left-associated source rewrite-step count is the first source count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
    triple

/-- Motive-root wrapper: left-associated target rewrite-step count is the third target count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
    triple

/-- Motive-root wrapper: right-associated source rewrite-step count is the first source count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
    triple

/-- Motive-root wrapper: right-associated target rewrite-step count is the third target count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
