import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.AdjacentCompositeTransport.Owner

/-!
# Public adjacent-pair transported composites inside composable triples

This file exposes adjacent-pair transported-composite formulas through the
public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left adjacent pair transported trace-hom formula. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_composedForward_traceHom_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.composedForward.traceHom =
      triple.leftPair.left.traceHom ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.leftPair.right.traceHom) :=
  TraceAnalyticMotive.composableTriple_leftPair_composedForward_traceHom_left_rightTransport
    triple

/-- Public wrapper: right adjacent pair transported trace-hom formula. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_composedForward_traceHom_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.composedForward.traceHom =
      triple.rightPair.left.traceHom ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.rightPair.right.traceHom) :=
  TraceAnalyticMotive.composableTriple_rightPair_composedForward_traceHom_left_rightTransport
    triple

/-- Public wrapper: left adjacent pair transported representable-map formula. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_composedForward_representableMap_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.composedForward.representableMap =
      triple.leftPair.left.map ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.leftPair.right.map) :=
  TraceAnalyticMotive.composableTriple_leftPair_composedForward_representableMap_left_rightTransport
    triple

/-- Public wrapper: right adjacent pair transported representable-map formula. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_composedForward_representableMap_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.composedForward.representableMap =
      triple.rightPair.left.map ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.rightPair.right.map) :=
  TraceAnalyticMotive.composableTriple_rightPair_composedForward_representableMap_left_rightTransport
    triple

end AnalyticMotives
end LFunctions
end Boundary
