import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Owner

/-!
# Endpoint counts of localized-arrow triple composites

This file records source and target count projections for the two named
localized-forward-arrow triple composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated localized-arrow composite keeps the first source imported count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.localizedForwardArrow.sourceImportedRectangleCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_sourceImportedRectangleCount
              (TraceLocalizationWordClass.comp
                triple.first.localizedForwardArrow
                triple.second.localizedForwardArrow)
              triple.third.localizedForwardArrow)
            (TraceLocalizationWordClass.comp_sourceImportedRectangleCount
              triple.first.localizedForwardArrow
              triple.second.localizedForwardArrow)

/-- The left-associated localized-arrow composite keeps the third target imported count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.localizedForwardArrow.targetImportedRectangleCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_targetImportedRectangleCount
            (TraceLocalizationWordClass.comp
              triple.first.localizedForwardArrow
              triple.second.localizedForwardArrow)
            triple.third.localizedForwardArrow

/-- The right-associated localized-arrow composite keeps the first source imported count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.localizedForwardArrow.sourceImportedRectangleCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_sourceImportedRectangleCount
            triple.first.localizedForwardArrow
            (TraceLocalizationWordClass.comp
              triple.second.localizedForwardArrow
              triple.third.localizedForwardArrow)

/-- The right-associated localized-arrow composite keeps the third target imported count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangleCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.localizedForwardArrow.targetImportedRectangleCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_targetImportedRectangleCount
              triple.first.localizedForwardArrow
              (TraceLocalizationWordClass.comp
                triple.second.localizedForwardArrow
                triple.third.localizedForwardArrow))
            (TraceLocalizationWordClass.comp_targetImportedRectangleCount
              triple.second.localizedForwardArrow
              triple.third.localizedForwardArrow)

/-- The left-associated localized-arrow composite keeps the first source bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.localizedForwardArrow.sourceTraceBookkeepingCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_sourceTraceBookkeepingCount
              (TraceLocalizationWordClass.comp
                triple.first.localizedForwardArrow
                triple.second.localizedForwardArrow)
              triple.third.localizedForwardArrow)
            (TraceLocalizationWordClass.comp_sourceTraceBookkeepingCount
              triple.first.localizedForwardArrow
              triple.second.localizedForwardArrow)

/-- The left-associated localized-arrow composite keeps the third target bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.localizedForwardArrow.targetTraceBookkeepingCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_targetTraceBookkeepingCount
            (TraceLocalizationWordClass.comp
              triple.first.localizedForwardArrow
              triple.second.localizedForwardArrow)
            triple.third.localizedForwardArrow

/-- The right-associated localized-arrow composite keeps the first source bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.localizedForwardArrow.sourceTraceBookkeepingCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_sourceTraceBookkeepingCount
            triple.first.localizedForwardArrow
            (TraceLocalizationWordClass.comp
              triple.second.localizedForwardArrow
              triple.third.localizedForwardArrow)

/-- The right-associated localized-arrow composite keeps the third target bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.localizedForwardArrow.targetTraceBookkeepingCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_targetTraceBookkeepingCount
              triple.first.localizedForwardArrow
              (TraceLocalizationWordClass.comp
                triple.second.localizedForwardArrow
                triple.third.localizedForwardArrow))
            (TraceLocalizationWordClass.comp_targetTraceBookkeepingCount
              triple.second.localizedForwardArrow
              triple.third.localizedForwardArrow)

end AnalyticMotives
end LFunctions
end Boundary
