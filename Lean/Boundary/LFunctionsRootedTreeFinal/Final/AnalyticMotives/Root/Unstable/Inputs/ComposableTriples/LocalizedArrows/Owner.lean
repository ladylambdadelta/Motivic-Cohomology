import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Owner

/-!
# Public localized-arrow associativity for composable triples

This file exposes named localized-forward-arrow associativity for composable
triples through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: named localized forward arrows of a composable triple associate. -/
theorem AnalyticMotivesRoot.localizedForwardArrow_assoc
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
  TraceAnalyticMotive.localizedForwardArrow_assoc
    triple

end AnalyticMotives
end LFunctions
end Boundary
