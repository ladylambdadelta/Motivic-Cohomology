import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.CategoryLaws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Owner

/-!
# Forward-word triples in the unstable category-law lane

This file connects unstable category-law associativity with the concrete
localized forward-word associativity of composable localization-input triples.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Category-law lane wrapper: unstable forward words of a composable triple associate. -/
theorem TraceUnstableAnalyticMotive.forwardWordTriple_assoc
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationWordClass.comp
          triple.first.unstableForward
          (match triple.first_middle_eq with
          | rfl => triple.second.unstableForward))
        (match triple.second_middle_eq with
        | rfl => triple.third.unstableForward) =
      TraceLocalizationWordClass.comp
        triple.first.unstableForward
        (TraceLocalizationWordClass.comp
          (match triple.first_middle_eq with
          | rfl => triple.second.unstableForward)
          (match triple.second_middle_eq with
          | rfl => triple.third.unstableForward)) :=
  TraceLocalizationInputComposableTriple.unstableForward_wordClass_assoc
    triple

end AnalyticMotives
end LFunctions
end Boundary
