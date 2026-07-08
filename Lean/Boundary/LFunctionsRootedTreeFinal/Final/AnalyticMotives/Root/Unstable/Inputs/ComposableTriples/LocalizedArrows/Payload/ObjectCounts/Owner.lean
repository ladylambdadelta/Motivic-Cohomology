import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.ObjectCounts.Owner

/-!
# Public object-level counts of localized-arrow triple composites

This file exposes object-level endpoint count facts for localized-forward-arrow
triple composites through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated source imported count is the first source count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
    triple

/-- Public wrapper: left-associated target imported count is the third target count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
    triple

/-- Public wrapper: right-associated source imported count is the first source count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
    triple

/-- Public wrapper: right-associated target imported count is the third target count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
    triple

/-- Public wrapper: left-associated source bookkeeping count is the first source count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
    triple

/-- Public wrapper: left-associated target bookkeeping count is the third target count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
    triple

/-- Public wrapper: right-associated source bookkeeping count is the first source count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
    triple

/-- Public wrapper: right-associated target bookkeeping count is the third target count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
    triple

/-- Public wrapper: left-associated source rewrite-step count is the first source count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
    triple

/-- Public wrapper: left-associated target rewrite-step count is the third target count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
    triple

/-- Public wrapper: right-associated source rewrite-step count is the first source count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
    triple

/-- Public wrapper: right-associated target rewrite-step count is the third target count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
