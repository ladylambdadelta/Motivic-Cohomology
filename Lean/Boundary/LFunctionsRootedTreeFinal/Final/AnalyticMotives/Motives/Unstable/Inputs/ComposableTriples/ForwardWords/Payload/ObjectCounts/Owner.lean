import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Owner

/-!
# Object-level counts of triple forward words

This file identifies the endpoint counts of the two unstable forward-word
parenthesizations with the first source object and third target object.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated triple forward word source imported count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (Eq.trans
              (TraceLocalizationWordClass.comp_sourceImportedRectangleCount
                (TraceLocalizationWordClass.comp
                  triple.first.unstableForward
                  triple.second.unstableForward)
                triple.third.unstableForward)
              (TraceLocalizationWordClass.comp_sourceImportedRectangleCount
                triple.first.unstableForward
                triple.second.unstableForward))
            (TraceLocalizationInput.unstableForward_sourceImportedRectangleCount
              triple.first)

/-- The left-associated triple forward word target imported count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_targetImportedRectangleCount
              (TraceLocalizationWordClass.comp
                triple.first.unstableForward
                triple.second.unstableForward)
              triple.third.unstableForward)
            (TraceLocalizationInput.unstableForward_targetImportedRectangleCount
              triple.third)

/-- The right-associated triple forward word source imported count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceImportedRectangleCount =
      triple.first.sourceObject.importedRectangleCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_sourceImportedRectangleCount
              triple.first.unstableForward
              (TraceLocalizationWordClass.comp
                triple.second.unstableForward
                triple.third.unstableForward))
            (TraceLocalizationInput.unstableForward_sourceImportedRectangleCount
              triple.first)

/-- The right-associated triple forward word target imported count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetImportedRectangleCount =
      triple.third.targetObject.importedRectangleCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (Eq.trans
              (TraceLocalizationWordClass.comp_targetImportedRectangleCount
                triple.first.unstableForward
                (TraceLocalizationWordClass.comp
                  triple.second.unstableForward
                  triple.third.unstableForward))
              (TraceLocalizationWordClass.comp_targetImportedRectangleCount
                triple.second.unstableForward
                triple.third.unstableForward))
            (TraceLocalizationInput.unstableForward_targetImportedRectangleCount
              triple.third)

/-- The left-associated triple forward word source bookkeeping count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
      triple)
    (TraceLocalizationInput.unstableForward_sourceTraceBookkeepingCount
      triple.first)

/-- The left-associated triple forward word target bookkeeping count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetTraceBookkeepingCount
      triple)
    (TraceLocalizationInput.unstableForward_targetTraceBookkeepingCount
      triple.third)

/-- The right-associated triple forward word source bookkeeping count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.sourceObject.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
      triple)
    (TraceLocalizationInput.unstableForward_sourceTraceBookkeepingCount
      triple.first)

/-- The right-associated triple forward word target bookkeeping count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetTraceBookkeepingObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.targetObject.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetTraceBookkeepingCount
      triple)
    (TraceLocalizationInput.unstableForward_targetTraceBookkeepingCount
      triple.third)

/-- The left-associated triple forward word source rewrite-step count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceRewriteStepCount
      triple)
    (TraceLocalizationInput.unstableForward_sourceRewriteStepCount
      triple.first)

/-- The left-associated triple forward word target rewrite-step count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetRewriteStepCount
      triple)
    (TraceLocalizationInput.unstableForward_targetRewriteStepCount
      triple.third)

/-- The right-associated triple forward word source rewrite-step count is the first source count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.sourceObject.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceRewriteStepCount
      triple)
    (TraceLocalizationInput.unstableForward_sourceRewriteStepCount
      triple.first)

/-- The right-associated triple forward word target rewrite-step count is the third target count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetRewriteStepObjectCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.targetObject.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetRewriteStepCount
      triple)
    (TraceLocalizationInput.unstableForward_targetRewriteStepCount
      triple.third)

end AnalyticMotives
end LFunctions
end Boundary
