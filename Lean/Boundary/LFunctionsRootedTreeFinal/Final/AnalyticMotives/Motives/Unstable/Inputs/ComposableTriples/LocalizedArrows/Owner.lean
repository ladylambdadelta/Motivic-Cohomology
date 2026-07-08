import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Owner

/-!
# Localized-arrow associativity for composable unstable input triples

This file states triple forward-arrow associativity using the named
`localizedForwardArrow` API of the localized-word category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The named localized forward arrows of a composable triple associate. -/
theorem TraceLocalizationInputComposableTriple.localizedForwardArrow_assoc
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationWordClass.comp
          triple.first.localizedForwardArrow
          (match triple.first_middle_eq with
          | rfl => triple.second.localizedForwardArrow))
        (match triple.second_middle_eq with
        | rfl => triple.third.localizedForwardArrow) =
      TraceLocalizationWordClass.comp
        triple.first.localizedForwardArrow
        (TraceLocalizationWordClass.comp
          (match triple.first_middle_eq with
          | rfl => triple.second.localizedForwardArrow)
          (match triple.second_middle_eq with
          | rfl => triple.third.localizedForwardArrow)) :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_assoc
            triple.first.localizedForwardArrow
            triple.second.localizedForwardArrow
            triple.third.localizedForwardArrow

end AnalyticMotives
end LFunctions
end Boundary
