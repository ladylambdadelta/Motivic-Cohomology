import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.CategoryLaws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.CompactInterpretation.Triples.Owner

/-!
# Compact-interpretation triples in the unstable category-law lane

This file connects unstable category-law associativity with the concrete
triple associativity of forward compact interpretations of localization inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Category-law lane wrapper: triple compact-interpretation trace homs associate. -/
theorem TraceUnstableAnalyticMotive.compactInterpretationTriple_traceHom_assoc
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

/-- Category-law lane wrapper: triple compact-interpretation representable maps associate. -/
theorem TraceUnstableAnalyticMotive.compactInterpretationTriple_representableMap_assoc
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
