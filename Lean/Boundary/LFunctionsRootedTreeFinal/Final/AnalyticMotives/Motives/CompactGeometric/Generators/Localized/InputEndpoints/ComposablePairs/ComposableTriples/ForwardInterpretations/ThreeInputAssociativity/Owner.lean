import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.ThreeInputFormulas.Owner

/-!
# Three-input associativity for composable-triple forward composites

This file records associativity after substituting the three underlying
localization inputs into the triple forward composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The two substituted three-input trace-hom parenthesizations agree. -/
theorem TraceLocalizationInputComposableTriple.associatedForward_traceHom_inputs_eq
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
  Eq.trans
    (Eq.symm
      (TraceLocalizationInputComposableTriple.leftAssociatedForward_traceHom_inputs
        triple))
    (Eq.trans
      (TraceLocalizationInputComposableTriple.associatedForward_traceHom_eq
        triple)
      (TraceLocalizationInputComposableTriple.rightAssociatedForward_traceHom_inputs
        triple))

/-- The two substituted three-input representable-map parenthesizations agree. -/
theorem TraceLocalizationInputComposableTriple.associatedForward_representableMap_inputs_eq
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
  Eq.trans
    (Eq.symm
      (TraceLocalizationInputComposableTriple.leftAssociatedForward_representableMap_inputs
        triple))
    (Eq.trans
      (TraceLocalizationInputComposableTriple.associatedForward_representableMap_eq
        triple)
      (TraceLocalizationInputComposableTriple.rightAssociatedForward_representableMap_inputs
        triple))

end AnalyticMotives
end LFunctions
end Boundary
