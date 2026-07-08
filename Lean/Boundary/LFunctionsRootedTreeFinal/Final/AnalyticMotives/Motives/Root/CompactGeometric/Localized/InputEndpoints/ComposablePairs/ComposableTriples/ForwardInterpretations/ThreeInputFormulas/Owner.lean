import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.ThreeInputFormulas.Owner

/-!
# Motive-root three-input formulas for composable-triple forward composites

This file exposes three-input trace-hom and representable-map formulas through
the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated trace-hom formula with input factors. -/
theorem TraceAnalyticMotive.composableTriple_leftAssociatedForward_traceHom_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.traceHom =
      (triple.first.traceHom ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.leftPair with
          | rfl => triple.second.traceHom)) ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.third.traceHom) :=
  TraceLocalizationInputComposableTriple.leftAssociatedForward_traceHom_inputs
    triple

/-- Motive-root wrapper: right-associated trace-hom formula with input factors. -/
theorem TraceAnalyticMotive.composableTriple_rightAssociatedForward_traceHom_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.traceHom =
      triple.first.traceHom ≫
        ((match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.second.traceHom) ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.rightPair with
          | rfl => triple.third.traceHom)) :=
  TraceLocalizationInputComposableTriple.rightAssociatedForward_traceHom_inputs
    triple

/-- Motive-root wrapper: left-associated representable-map formula with input factors. -/
theorem TraceAnalyticMotive.composableTriple_leftAssociatedForward_representableMap_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.representableMap =
      (triple.first.map ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.leftPair with
          | rfl => triple.second.map)) ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.third.map) :=
  TraceLocalizationInputComposableTriple.leftAssociatedForward_representableMap_inputs
    triple

/-- Motive-root wrapper: right-associated representable-map formula with input factors. -/
theorem TraceAnalyticMotive.composableTriple_rightAssociatedForward_representableMap_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.representableMap =
      triple.first.map ≫
        ((match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.second.map) ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.rightPair with
          | rfl => triple.third.map)) :=
  TraceLocalizationInputComposableTriple.rightAssociatedForward_representableMap_inputs
    triple

end AnalyticMotives
end LFunctions
end Boundary
