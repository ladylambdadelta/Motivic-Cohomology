import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Owner

/-!
# Motive-root forward words of composable unstable input triples

This file exposes localized forward-word associativity for composable triples
through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the three forward input word classes of a composable triple associate. -/
theorem TraceAnalyticMotive.forwardWordClass_assoc
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationWordClass.comp
          (TraceLocalizationWordClass.ofInputForward triple.first)
          (match triple.first_middle_eq with
          | rfl => TraceLocalizationWordClass.ofInputForward triple.second))
        (match triple.second_middle_eq with
        | rfl => TraceLocalizationWordClass.ofInputForward triple.third) =
      TraceLocalizationWordClass.comp
        (TraceLocalizationWordClass.ofInputForward triple.first)
        (TraceLocalizationWordClass.comp
          (match triple.first_middle_eq with
          | rfl => TraceLocalizationWordClass.ofInputForward triple.second)
          (match triple.second_middle_eq with
          | rfl => TraceLocalizationWordClass.ofInputForward triple.third)) :=
  TraceLocalizationInputComposableTriple.forwardWordClass_assoc
    triple

/-- Motive-root wrapper: the three unstable forward arrows associate as localized words. -/
theorem TraceAnalyticMotive.unstableForward_wordClass_assoc
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationWordClass.comp
          triple.first.unstableForward
          (match triple.first_middle_eq with
          | rfl => triple.second.unstableForward))
        (match triple.second_middle_eq with
        | rfl => triple.third.unstableForward) =
      TraceLocalizationWordClass.comp
        triple.first.unstableForward
        (TraceLocalizationWordClass.comp
          (match triple.first_middle_eq with
          | rfl => triple.second.unstableForward)
          (match triple.second_middle_eq with
          | rfl => triple.third.unstableForward)) :=
  TraceLocalizationInputComposableTriple.unstableForward_wordClass_assoc
    triple

end AnalyticMotives
end LFunctions
end Boundary
