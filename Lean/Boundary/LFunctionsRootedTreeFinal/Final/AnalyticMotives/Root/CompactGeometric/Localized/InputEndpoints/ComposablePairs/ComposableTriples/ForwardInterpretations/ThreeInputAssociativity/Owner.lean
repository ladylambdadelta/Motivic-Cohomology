import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.ThreeInputAssociativity.Owner

/-!
# Public three-input associativity for composable-triple forward composites

This file exposes substituted three-input associativity through the public root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: substituted three-input trace-hom associativity. -/
theorem AnalyticMotivesRoot.composableTriple_associatedForward_traceHom_inputs_eq
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.first.traceHom ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.second.traceHom)) ≫
      (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.rightPair with
      | rfl => triple.third.traceHom) =
    triple.first.traceHom ≫
      ((match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.leftPair with
      | rfl => triple.second.traceHom) ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.third.traceHom)) :=
  TraceAnalyticMotive.composableTriple_associatedForward_traceHom_inputs_eq
    triple

/-- Public wrapper: substituted three-input representable-map associativity. -/
theorem AnalyticMotivesRoot.composableTriple_associatedForward_representableMap_inputs_eq
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.first.map ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.second.map)) ≫
      (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.rightPair with
      | rfl => triple.third.map) =
    triple.first.map ≫
      ((match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.leftPair with
      | rfl => triple.second.map) ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.third.map)) :=
  TraceAnalyticMotive.composableTriple_associatedForward_representableMap_inputs_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
