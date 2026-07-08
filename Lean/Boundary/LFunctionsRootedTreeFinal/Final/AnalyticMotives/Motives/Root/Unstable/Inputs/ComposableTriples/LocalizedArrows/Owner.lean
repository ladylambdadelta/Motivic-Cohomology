import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Owner

/-!
# Motive-root localized-arrow associativity for composable triples

This file exposes named localized-forward-arrow associativity for composable
triples through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: named localized forward arrows of a composable triple associate. -/
theorem TraceAnalyticMotive.localizedForwardArrow_assoc
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
  TraceLocalizationInputComposableTriple.localizedForwardArrow_assoc
    triple

end AnalyticMotives
end LFunctions
end Boundary
