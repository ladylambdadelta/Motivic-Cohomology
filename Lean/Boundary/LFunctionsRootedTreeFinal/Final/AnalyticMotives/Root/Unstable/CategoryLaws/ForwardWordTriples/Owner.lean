import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.CategoryLaws.ForwardWordTriples.Owner

/-!
# Public forward-word triples in the unstable category-law lane

This file exposes category-law lane wrappers for localized forward-word
associativity through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: unstable forward words of a composable triple associate. -/
theorem AnalyticMotivesRoot.unstableCategory_forwardWordTriple_assoc
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
  TraceAnalyticMotive.unstableCategory_forwardWordTriple_assoc
    triple

end AnalyticMotives
end LFunctions
end Boundary
