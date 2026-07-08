import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.Owner

/-!
# Transported right forward maps in composable input pairs

This file projects the right-forward endpoint transport of a composable pair
through trace homs, representable maps, and functorial views.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The transported right forward map has the transported right-input trace hom. -/
theorem TraceLocalizationInputComposablePair.rightForward_traceHom_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward.traceHom =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.traceHom :=
  match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
  | rfl =>
      TraceLocalizationInputComposablePair.rightForwardBeforeTransport_traceHom
        pair

/-- The transported right forward map has the transported right-input representable map. -/
theorem TraceLocalizationInputComposablePair.rightForward_representableMap_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward.representableMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.map :=
  match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
  | rfl =>
      TraceLocalizationInputComposablePair.rightForwardBeforeTransport_representableMap
        pair

/-- The presheaf functor sees the transported right forward map as the transported right input map. -/
theorem TraceLocalizationInputComposablePair.rightForward_presheafFunctor_map_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map pair.rightForward =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.map :=
  match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
  | rfl =>
      TraceLocalizationInputComposablePair.rightForwardBeforeTransport_presheafFunctor_map
        pair

/-- The lifted transported right forward map is the transported Yoneda map of the right trace hom. -/
theorem TraceLocalizationInputComposablePair.rightForward_representableObjectMap_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward.representableObjectMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => (TraceCorQRepresentablePresheaf.yoneda).map pair.right.traceHom :=
  match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
  | rfl =>
      TraceLocalizationInputComposablePair.rightForwardBeforeTransport_representableObjectMap_eq_yoneda
        pair

/-- Including the transported lifted right forward map recovers the transported right input map. -/
theorem TraceLocalizationInputComposablePair.rightForward_representableObjectMap_inclusion_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQRepresentablePresheaf.inclusion.map
        pair.rightForward.representableObjectMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.right.map :=
  match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
  | rfl =>
      TraceLocalizationInputComposablePair.rightForwardBeforeTransport_representableObjectMap_inclusion
        pair

end AnalyticMotives
end LFunctions
end Boundary
