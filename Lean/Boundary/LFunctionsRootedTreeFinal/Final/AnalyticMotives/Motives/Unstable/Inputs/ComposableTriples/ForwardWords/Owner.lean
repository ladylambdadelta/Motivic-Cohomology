import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Representatives.Owner

/-!
# Forward words of composable unstable input triples

This file records associativity for the actual localized forward word classes
attached to a composable triple of localization inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The three forward input word classes of a composable triple associate. -/
theorem TraceLocalizationInputComposableTriple.forwardWordClass_assoc
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
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_assoc
            (TraceLocalizationWordClass.ofInputForward triple.first)
            (TraceLocalizationWordClass.ofInputForward triple.second)
            (TraceLocalizationWordClass.ofInputForward triple.third)

/-- The three unstable forward arrows of a composable triple associate as localized words. -/
theorem TraceLocalizationInputComposableTriple.unstableForward_wordClass_assoc
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
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_assoc
            triple.first.unstableForward
            triple.second.unstableForward
            triple.third.unstableForward

end AnalyticMotives
end LFunctions
end Boundary
