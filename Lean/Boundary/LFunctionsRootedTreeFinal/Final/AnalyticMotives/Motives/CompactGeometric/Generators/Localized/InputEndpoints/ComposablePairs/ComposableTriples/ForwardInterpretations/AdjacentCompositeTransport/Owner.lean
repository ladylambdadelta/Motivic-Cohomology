import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.ComposedTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.Owner

/-!
# Adjacent-pair transported composites inside composable triples

This file applies the pair-level transported-composite formulas to the two
adjacent composable pairs carried by a composable triple.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left adjacent pair composite has its transported trace-hom formula. -/
theorem TraceLocalizationInputComposableTriple.leftPair_composedForward_traceHom_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.composedForward.traceHom =
      triple.leftPair.left.traceHom ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.leftPair.right.traceHom) :=
  TraceLocalizationInputComposablePair.composedForward_traceHom_left_rightTransport
    triple.leftPair

/-- The right adjacent pair composite has its transported trace-hom formula. -/
theorem TraceLocalizationInputComposableTriple.rightPair_composedForward_traceHom_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.composedForward.traceHom =
      triple.rightPair.left.traceHom ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.rightPair.right.traceHom) :=
  TraceLocalizationInputComposablePair.composedForward_traceHom_left_rightTransport
    triple.rightPair

/-- The left adjacent pair composite has its transported representable-map formula. -/
theorem TraceLocalizationInputComposableTriple.leftPair_composedForward_representableMap_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.composedForward.representableMap =
      triple.leftPair.left.map ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.leftPair.right.map) :=
  TraceLocalizationInputComposablePair.composedForward_representableMap_left_rightTransport
    triple.leftPair

/-- The right adjacent pair composite has its transported representable-map formula. -/
theorem TraceLocalizationInputComposableTriple.rightPair_composedForward_representableMap_left_rightTransport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.composedForward.representableMap =
      triple.rightPair.left.map ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.rightPair.right.map) :=
  TraceLocalizationInputComposablePair.composedForward_representableMap_left_rightTransport
    triple.rightPair

end AnalyticMotives
end LFunctions
end Boundary
