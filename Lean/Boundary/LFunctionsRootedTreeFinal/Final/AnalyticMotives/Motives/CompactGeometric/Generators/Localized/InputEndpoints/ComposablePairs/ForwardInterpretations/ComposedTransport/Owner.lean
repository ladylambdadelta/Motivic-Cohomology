import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.RightTransport.Owner

/-!
# Transported composite formulas for composable input pairs

This file records the composed forward map after substituting the transported
right forward factor through trace homs and representable maps.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The composed forward trace hom has the left input trace hom and transported right trace hom. -/
theorem TraceLocalizationInputComposablePair.composedForward_traceHom_left_rightTransport
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.traceHom =
      pair.left.traceHom ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
        | rfl => pair.right.traceHom) :=
  Eq.trans
    (TraceLocalizationInputComposablePair.composedForward_traceHom_left pair)
    (congrArg
      (fun traceHom =>
        pair.left.traceHom ≫ traceHom)
      (TraceLocalizationInputComposablePair.rightForward_traceHom_eq_transport pair))

/-- The composed forward representable map has the left input map and transported right map. -/
theorem TraceLocalizationInputComposablePair.composedForward_representableMap_left_rightTransport
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.representableMap =
      pair.left.map ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
        | rfl => pair.right.map) :=
  Eq.trans
    (TraceLocalizationInputComposablePair.composedForward_representableMap_left pair)
    (congrArg
      (fun map =>
        pair.left.map ≫ map)
      (TraceLocalizationInputComposablePair.rightForward_representableMap_eq_transport pair))

end AnalyticMotives
end LFunctions
end Boundary
