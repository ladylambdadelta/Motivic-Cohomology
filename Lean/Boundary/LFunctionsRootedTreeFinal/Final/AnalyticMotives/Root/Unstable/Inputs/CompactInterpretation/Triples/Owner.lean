import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CompactInterpretation.Triples.Owner

/-!
# Public triple associativity for unstable compact interpretations

This file exposes triple associativity for unstable forward compact
interpretations through the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: triple unstable forward compact interpretations associate on trace homs. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_triple_traceHom_assoc
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
  TraceAnalyticMotive.unstableForwardCompactInterpretation_triple_traceHom_assoc
    triple

/-- Public wrapper: triple unstable forward compact interpretations associate on maps. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_triple_representableMap_assoc
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
  TraceAnalyticMotive.unstableForwardCompactInterpretation_triple_representableMap_assoc
    triple

end AnalyticMotives
end LFunctions
end Boundary
