import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Counts.Owner

/-!
# Endpoint rewrite-step counts of localized-arrow triple composites

This file records source and target rewrite-step count projections for the two
named localized-forward-arrow triple composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated localized-arrow composite keeps the first source rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.localizedForwardArrow.sourceRewriteStepCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_sourceRewriteStepCount
              (TraceLocalizationWordClass.comp
                triple.first.localizedForwardArrow
                triple.second.localizedForwardArrow)
              triple.third.localizedForwardArrow)
            (TraceLocalizationWordClass.comp_sourceRewriteStepCount
              triple.first.localizedForwardArrow
              triple.second.localizedForwardArrow)

/-- The left-associated localized-arrow composite keeps the third target rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.localizedForwardArrow.targetRewriteStepCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_targetRewriteStepCount
            (TraceLocalizationWordClass.comp
              triple.first.localizedForwardArrow
              triple.second.localizedForwardArrow)
            triple.third.localizedForwardArrow

/-- The right-associated localized-arrow composite keeps the first source rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.localizedForwardArrow.sourceRewriteStepCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_sourceRewriteStepCount
            triple.first.localizedForwardArrow
            (TraceLocalizationWordClass.comp
              triple.second.localizedForwardArrow
              triple.third.localizedForwardArrow)

/-- The right-associated localized-arrow composite keeps the third target rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.localizedForwardArrow.targetRewriteStepCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_targetRewriteStepCount
              triple.first.localizedForwardArrow
              (TraceLocalizationWordClass.comp
                triple.second.localizedForwardArrow
                triple.third.localizedForwardArrow))
            (TraceLocalizationWordClass.comp_targetRewriteStepCount
              triple.second.localizedForwardArrow
              triple.third.localizedForwardArrow)

end AnalyticMotives
end LFunctions
end Boundary
