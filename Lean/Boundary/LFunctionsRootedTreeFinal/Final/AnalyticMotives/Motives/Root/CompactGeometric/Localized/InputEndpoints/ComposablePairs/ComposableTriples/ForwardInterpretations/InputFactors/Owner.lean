import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.InputFactors.Owner

/-!
# Motive-root input factors of composable-triple forward interpretations

This file exposes triple forward-factor identifications through the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: first forward factor trace hom. -/
theorem TraceAnalyticMotive.composableTriple_firstForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstForward.traceHom =
      triple.first.traceHom :=
  TraceLocalizationInputComposableTriple.firstForward_traceHom
    triple

/-- Motive-root wrapper: first forward factor representable map. -/
theorem TraceAnalyticMotive.composableTriple_firstForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstForward.representableMap =
      triple.first.map :=
  TraceLocalizationInputComposableTriple.firstForward_representableMap
    triple

/-- Motive-root wrapper: transported second forward factor trace hom. -/
theorem TraceAnalyticMotive.composableTriple_secondForward_traceHom_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondForward.traceHom =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.leftPair with
      | rfl => triple.second.traceHom :=
  TraceLocalizationInputComposableTriple.secondForward_traceHom_eq_transport
    triple

/-- Motive-root wrapper: transported second forward factor representable map. -/
theorem TraceAnalyticMotive.composableTriple_secondForward_representableMap_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondForward.representableMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.leftPair with
      | rfl => triple.second.map :=
  TraceLocalizationInputComposableTriple.secondForward_representableMap_eq_transport
    triple

/-- Motive-root wrapper: transported third forward factor trace hom. -/
theorem TraceAnalyticMotive.composableTriple_thirdForward_traceHom_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.thirdForward.traceHom =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.rightPair with
      | rfl => triple.third.traceHom :=
  TraceLocalizationInputComposableTriple.thirdForward_traceHom_eq_transport
    triple

/-- Motive-root wrapper: transported third forward factor representable map. -/
theorem TraceAnalyticMotive.composableTriple_thirdForward_representableMap_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.thirdForward.representableMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.rightPair with
      | rfl => triple.third.map :=
  TraceLocalizationInputComposableTriple.thirdForward_representableMap_eq_transport
    triple

end AnalyticMotives
end LFunctions
end Boundary
