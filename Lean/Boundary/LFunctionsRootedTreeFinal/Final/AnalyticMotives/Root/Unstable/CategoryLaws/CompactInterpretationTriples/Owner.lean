import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.CategoryLaws.CompactInterpretationTriples.Owner

/-!
# Public compact-interpretation triples in the unstable category-law lane

This file exposes category-law lane wrappers for triple compact-interpretation
associativity through the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: triple compact-interpretation trace homs associate. -/
theorem AnalyticMotivesRoot.unstableCategory_compactInterpretationTriple_traceHom_assoc
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
  TraceAnalyticMotive.unstableCategory_compactInterpretationTriple_traceHom_assoc
    triple

/-- Public wrapper: triple compact-interpretation representable maps associate. -/
theorem AnalyticMotivesRoot.unstableCategory_compactInterpretationTriple_representableMap_assoc
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
  TraceAnalyticMotive.unstableCategory_compactInterpretationTriple_representableMap_assoc
    triple

end AnalyticMotives
end LFunctions
end Boundary
