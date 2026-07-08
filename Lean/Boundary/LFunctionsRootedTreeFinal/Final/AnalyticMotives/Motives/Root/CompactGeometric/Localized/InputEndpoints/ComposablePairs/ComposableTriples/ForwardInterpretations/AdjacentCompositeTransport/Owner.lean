import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.AdjacentCompositeTransport.Owner

/-!
# Motive-root adjacent-pair transported composites inside composable triples

This file exposes adjacent-pair transported-composite formulas through the
motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left adjacent pair transported trace-hom formula. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_composedForward_traceHom_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.composedForward.traceHom =
      triple.leftPair.left.traceHom ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.leftPair.right.traceHom) :=
  TraceLocalizationInputComposableTriple.leftPair_composedForward_traceHom_left_rightTransport
    triple

/-- Motive-root wrapper: right adjacent pair transported trace-hom formula. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_composedForward_traceHom_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.composedForward.traceHom =
      triple.rightPair.left.traceHom ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.rightPair.right.traceHom) :=
  TraceLocalizationInputComposableTriple.rightPair_composedForward_traceHom_left_rightTransport
    triple

/-- Motive-root wrapper: left adjacent pair transported representable-map formula. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_composedForward_representableMap_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.composedForward.representableMap =
      triple.leftPair.left.map ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.leftPair.right.map) :=
  TraceLocalizationInputComposableTriple.leftPair_composedForward_representableMap_left_rightTransport
    triple

/-- Motive-root wrapper: right adjacent pair transported representable-map formula. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_composedForward_representableMap_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.composedForward.representableMap =
      triple.rightPair.left.map ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.rightPair.right.map) :=
  TraceLocalizationInputComposableTriple.rightPair_composedForward_representableMap_left_rightTransport
    triple

end AnalyticMotives
end LFunctions
end Boundary
