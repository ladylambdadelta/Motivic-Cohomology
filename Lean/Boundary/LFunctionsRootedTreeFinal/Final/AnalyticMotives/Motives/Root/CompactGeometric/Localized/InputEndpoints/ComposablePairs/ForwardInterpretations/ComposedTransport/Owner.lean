import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.ComposedTransport.Owner

/-!
# Motive-root transported composite formulas for composable input pairs

This file exposes transported composite formulas through the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: composed trace hom with transported right factor. -/
theorem TraceAnalyticMotive.composablePair_composedForward_traceHom_left_rightTransport
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.traceHom =
      pair.left.traceHom ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
        | rfl => pair.right.traceHom) :=
  TraceLocalizationInputComposablePair.composedForward_traceHom_left_rightTransport
    pair

/-- Motive-root wrapper: composed representable map with transported right factor. -/
theorem TraceAnalyticMotive.composablePair_composedForward_representableMap_left_rightTransport
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.representableMap =
      pair.left.map ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
        | rfl => pair.right.map) :=
  TraceLocalizationInputComposablePair.composedForward_representableMap_left_rightTransport
    pair

end AnalyticMotives
end LFunctions
end Boundary
