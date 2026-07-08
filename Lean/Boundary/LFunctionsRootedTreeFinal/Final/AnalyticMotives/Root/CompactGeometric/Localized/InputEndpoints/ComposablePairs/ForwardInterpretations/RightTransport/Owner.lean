import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.RightTransport.Owner

/-!
# Public transported right forward maps in composable input pairs

This file exposes transported-right-forward projection facts through the public
root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: transported right forward trace hom. -/
theorem AnalyticMotivesRoot.composablePair_rightForward_traceHom_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward.traceHom =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.traceHom :=
  TraceAnalyticMotive.composablePair_rightForward_traceHom_eq_transport
    pair

/-- Public wrapper: transported right forward representable map. -/
theorem AnalyticMotivesRoot.composablePair_rightForward_representableMap_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward.representableMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.map :=
  TraceAnalyticMotive.composablePair_rightForward_representableMap_eq_transport
    pair

/-- Public wrapper: presheaf functor on the transported right forward map. -/
theorem AnalyticMotivesRoot.composablePair_rightForward_presheafFunctor_map_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map pair.rightForward =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.map :=
  TraceAnalyticMotive.composablePair_rightForward_presheafFunctor_map_eq_transport
    pair

/-- Public wrapper: lifted transported right forward map. -/
theorem AnalyticMotivesRoot.composablePair_rightForward_representableObjectMap_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward.representableObjectMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => (TraceCorQRepresentablePresheaf.yoneda).map pair.right.traceHom :=
  TraceAnalyticMotive.composablePair_rightForward_representableObjectMap_eq_transport
    pair

/-- Public wrapper: inclusion of the lifted transported right forward map. -/
theorem AnalyticMotivesRoot.composablePair_rightForward_representableObjectMap_inclusion_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQRepresentablePresheaf.inclusion.map
        pair.rightForward.representableObjectMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.map :=
  TraceAnalyticMotive.composablePair_rightForward_representableObjectMap_inclusion_eq_transport
    pair

end AnalyticMotives
end LFunctions
end Boundary
