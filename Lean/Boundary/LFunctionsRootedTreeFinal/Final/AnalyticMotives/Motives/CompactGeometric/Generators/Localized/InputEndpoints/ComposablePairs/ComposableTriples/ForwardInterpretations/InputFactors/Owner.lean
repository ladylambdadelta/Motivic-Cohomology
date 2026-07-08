import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.RightTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.Owner

/-!
# Input factors of composable-triple forward interpretations

This file identifies the three forward factors of a composable triple with the
underlying localization-input trace homs and representable maps.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The first triple forward factor has the first input trace hom. -/
theorem TraceLocalizationInputComposableTriple.firstForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstForward.traceHom =
      triple.first.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_traceHom
    triple.first

/-- The first triple forward factor has the first input representable map. -/
theorem TraceLocalizationInputComposableTriple.firstForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstForward.representableMap =
      triple.first.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_representableMap
    triple.first

/-- The second triple forward factor has the transported second input trace hom. -/
theorem TraceLocalizationInputComposableTriple.secondForward_traceHom_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondForward.traceHom =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.leftPair with
      | rfl => triple.second.traceHom :=
  match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
      triple.leftPair with
  | rfl =>
      TraceLocalizationInput.unstableForwardCompactInterpretation_traceHom
        triple.second

/-- The second triple forward factor has the transported second input representable map. -/
theorem TraceLocalizationInputComposableTriple.secondForward_representableMap_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondForward.representableMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.leftPair with
      | rfl => triple.second.map :=
  match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
      triple.leftPair with
  | rfl =>
      TraceLocalizationInput.unstableForwardCompactInterpretation_representableMap
        triple.second

/-- The third triple forward factor has the transported third input trace hom. -/
theorem TraceLocalizationInputComposableTriple.thirdForward_traceHom_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.thirdForward.traceHom =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.rightPair with
      | rfl => triple.third.traceHom :=
  match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
      triple.rightPair with
  | rfl =>
      TraceLocalizationInput.unstableForwardCompactInterpretation_traceHom
        triple.third

/-- The third triple forward factor has the transported third input representable map. -/
theorem TraceLocalizationInputComposableTriple.thirdForward_representableMap_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.thirdForward.representableMap =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
          triple.rightPair with
      | rfl => triple.third.map :=
  match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
      triple.rightPair with
  | rfl =>
      TraceLocalizationInput.unstableForwardCompactInterpretation_representableMap
        triple.third

end AnalyticMotives
end LFunctions
end Boundary
