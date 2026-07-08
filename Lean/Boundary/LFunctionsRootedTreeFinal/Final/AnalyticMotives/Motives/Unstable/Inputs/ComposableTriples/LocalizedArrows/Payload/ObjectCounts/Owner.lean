import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Counts.RewriteSteps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.TraceCalculus.Counts.Owner

/-!
# Object-level counts of localized-arrow triple composites

This file identifies endpoint counts of the two named localized-forward-arrow
parenthesizations with the first source object and third target object.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated localized-arrow source imported count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
      triple.first)

/-- The left-associated localized-arrow target imported count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangleCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
      triple.third)

/-- The right-associated localized-arrow source imported count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
      triple.first)

/-- The right-associated localized-arrow target imported count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangleCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
      triple.third)

/-- The left-associated localized-arrow source bookkeeping count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount
      triple.first)

/-- The left-associated localized-arrow target bookkeeping count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount
      triple.third)

/-- The right-associated localized-arrow source bookkeeping count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_sourceTraceBookkeepingCount
      triple.first)

/-- The right-associated localized-arrow target bookkeeping count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_targetTraceBookkeepingCount
      triple.third)

/-- The left-associated localized-arrow source rewrite-step count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceRewriteStepCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount
      triple.first)

/-- The left-associated localized-arrow target rewrite-step count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetRewriteStepCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount
      triple.third)

/-- The right-associated localized-arrow source rewrite-step count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceRewriteStepCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_sourceRewriteStepCount
      triple.first)

/-- The right-associated localized-arrow target rewrite-step count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetRewriteStepCount
      triple)
    (TraceLocalizationInput.localizedForwardArrow_targetRewriteStepCount
      triple.third)

end AnalyticMotives
end LFunctions
end Boundary
