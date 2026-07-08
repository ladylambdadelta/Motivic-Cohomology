import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.CompactInterpretation.Triples.Owner

/-!
# Motive-root triple associativity for unstable compact interpretations

This file exposes triple associativity for unstable forward compact
interpretations through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: triple unstable forward compact interpretations associate on trace homs. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_triple_traceHom_assoc
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
  TraceLocalizationInputComposableTriple.unstableForwardCompactInterpretation_traceHom_assoc
    triple

/-- Motive-root wrapper: triple unstable forward compact interpretations associate on maps. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_triple_representableMap_assoc
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
  TraceLocalizationInputComposableTriple.unstableForwardCompactInterpretation_representableMap_assoc
    triple

end AnalyticMotives
end LFunctions
end Boundary
