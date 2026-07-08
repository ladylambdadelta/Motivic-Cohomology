import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.RightTransport.Owner

/-!
# Motive-root transported right forward maps in composable input pairs

This file exposes transported-right-forward projection facts through the
motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: transported right forward trace hom. -/
theorem TraceAnalyticMotive.composablePair_rightForward_traceHom_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward.traceHom =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.traceHom :=
  TraceLocalizationInputComposablePair.rightForward_traceHom_eq_transport
    pair

/-- Motive-root wrapper: transported right forward representable map. -/
theorem TraceAnalyticMotive.composablePair_rightForward_representableMap_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward.representableMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.map :=
  TraceLocalizationInputComposablePair.rightForward_representableMap_eq_transport
    pair

/-- Motive-root wrapper: presheaf functor on the transported right forward map. -/
theorem TraceAnalyticMotive.composablePair_rightForward_presheafFunctor_map_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map pair.rightForward =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.map :=
  TraceLocalizationInputComposablePair.rightForward_presheafFunctor_map_eq_transport
    pair

/-- Motive-root wrapper: lifted transported right forward map. -/
theorem TraceAnalyticMotive.composablePair_rightForward_representableObjectMap_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward.representableObjectMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => (TraceCorQRepresentablePresheaf.yoneda).map pair.right.traceHom :=
  TraceLocalizationInputComposablePair.rightForward_representableObjectMap_eq_transport
    pair

/-- Motive-root wrapper: inclusion of the lifted transported right forward map. -/
theorem TraceAnalyticMotive.composablePair_rightForward_representableObjectMap_inclusion_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQRepresentablePresheaf.inclusion.map
        pair.rightForward.representableObjectMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.map :=
  TraceLocalizationInputComposablePair.rightForward_representableObjectMap_inclusion_eq_transport
    pair

end AnalyticMotives
end LFunctions
end Boundary
