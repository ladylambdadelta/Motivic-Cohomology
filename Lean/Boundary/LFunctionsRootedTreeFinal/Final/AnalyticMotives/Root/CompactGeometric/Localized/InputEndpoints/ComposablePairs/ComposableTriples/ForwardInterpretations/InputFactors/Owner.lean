import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.InputFactors.Owner

/-!
# Public input factors of composable-triple forward interpretations

This file exposes triple forward-factor identifications through the public root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: first forward factor trace hom. -/
theorem AnalyticMotivesRoot.composableTriple_firstForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstForward.traceHom =
      triple.first.traceHom :=
  TraceAnalyticMotive.composableTriple_firstForward_traceHom
    triple

/-- Public wrapper: first forward factor representable map. -/
theorem AnalyticMotivesRoot.composableTriple_firstForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstForward.representableMap =
      triple.first.map :=
  TraceAnalyticMotive.composableTriple_firstForward_representableMap
    triple

/-- Public wrapper: transported second forward factor trace hom. -/
theorem AnalyticMotivesRoot.composableTriple_secondForward_traceHom_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondForward.traceHom =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.leftPair with
      | rfl => triple.second.traceHom :=
  TraceAnalyticMotive.composableTriple_secondForward_traceHom_eq_transport
    triple

/-- Public wrapper: transported second forward factor representable map. -/
theorem AnalyticMotivesRoot.composableTriple_secondForward_representableMap_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondForward.representableMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.leftPair with
      | rfl => triple.second.map :=
  TraceAnalyticMotive.composableTriple_secondForward_representableMap_eq_transport
    triple

/-- Public wrapper: transported third forward factor trace hom. -/
theorem AnalyticMotivesRoot.composableTriple_thirdForward_traceHom_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.thirdForward.traceHom =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.rightPair with
      | rfl => triple.third.traceHom :=
  TraceAnalyticMotive.composableTriple_thirdForward_traceHom_eq_transport
    triple

/-- Public wrapper: transported third forward factor representable map. -/
theorem AnalyticMotivesRoot.composableTriple_thirdForward_representableMap_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.thirdForward.representableMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.rightPair with
      | rfl => triple.third.map :=
  TraceAnalyticMotive.composableTriple_thirdForward_representableMap_eq_transport
    triple

end AnalyticMotives
end LFunctions
end Boundary
