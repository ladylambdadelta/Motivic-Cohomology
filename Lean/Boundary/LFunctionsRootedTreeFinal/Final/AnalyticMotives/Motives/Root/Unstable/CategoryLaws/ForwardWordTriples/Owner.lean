import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.CategoryLaws.ForwardWordTriples.Owner

/-!
# Motive-root forward-word triples in the unstable category-law lane

This file exposes category-law lane wrappers for localized forward-word
associativity through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: unstable forward words of a composable triple associate. -/
theorem TraceAnalyticMotive.unstableCategory_forwardWordTriple_assoc
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
  TraceUnstableAnalyticMotive.forwardWordTriple_assoc
    triple

end AnalyticMotives
end LFunctions
end Boundary
