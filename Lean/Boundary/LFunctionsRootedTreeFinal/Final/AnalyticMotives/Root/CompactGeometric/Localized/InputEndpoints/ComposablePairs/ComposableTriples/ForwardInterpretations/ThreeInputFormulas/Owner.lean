import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.ThreeInputFormulas.Owner

/-!
# Public three-input formulas for composable-triple forward composites

This file exposes three-input trace-hom and representable-map formulas through
the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated trace-hom formula with input factors. -/
theorem AnalyticMotivesRoot.composableTriple_leftAssociatedForward_traceHom_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.traceHom =
      (triple.first.traceHom ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.leftPair with
          | rfl => triple.second.traceHom)) ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.third.traceHom) :=
  TraceAnalyticMotive.composableTriple_leftAssociatedForward_traceHom_inputs
    triple

/-- Public wrapper: right-associated trace-hom formula with input factors. -/
theorem AnalyticMotivesRoot.composableTriple_rightAssociatedForward_traceHom_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.traceHom =
      triple.first.traceHom ≫
        ((match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.second.traceHom) ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.rightPair with
          | rfl => triple.third.traceHom)) :=
  TraceAnalyticMotive.composableTriple_rightAssociatedForward_traceHom_inputs
    triple

/-- Public wrapper: left-associated representable-map formula with input factors. -/
theorem AnalyticMotivesRoot.composableTriple_leftAssociatedForward_representableMap_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.representableMap =
      (triple.first.map ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.leftPair with
          | rfl => triple.second.map)) ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.third.map) :=
  TraceAnalyticMotive.composableTriple_leftAssociatedForward_representableMap_inputs
    triple

/-- Public wrapper: right-associated representable-map formula with input factors. -/
theorem AnalyticMotivesRoot.composableTriple_rightAssociatedForward_representableMap_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.representableMap =
      triple.first.map ≫
        ((match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.second.map) ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.rightPair with
          | rfl => triple.third.map)) :=
  TraceAnalyticMotive.composableTriple_rightAssociatedForward_representableMap_inputs
    triple

end AnalyticMotives
end LFunctions
end Boundary
