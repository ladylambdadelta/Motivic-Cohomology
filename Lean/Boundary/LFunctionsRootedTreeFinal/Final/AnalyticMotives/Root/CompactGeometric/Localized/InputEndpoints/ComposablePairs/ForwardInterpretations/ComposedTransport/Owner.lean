import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.ComposedTransport.Owner

/-!
# Public transported composite formulas for composable input pairs

This file exposes transported composite formulas through the public root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: composed trace hom with transported right factor. -/
theorem AnalyticMotivesRoot.composablePair_composedForward_traceHom_left_rightTransport
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.traceHom =
      pair.left.traceHom ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
        | rfl => pair.right.traceHom) :=
  TraceAnalyticMotive.composablePair_composedForward_traceHom_left_rightTransport
    pair

/-- Public wrapper: composed representable map with transported right factor. -/
theorem AnalyticMotivesRoot.composablePair_composedForward_representableMap_left_rightTransport
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.representableMap =
      pair.left.map ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
        | rfl => pair.right.map) :=
  TraceAnalyticMotive.composablePair_composedForward_representableMap_left_rightTransport
    pair

end AnalyticMotives
end LFunctions
end Boundary
