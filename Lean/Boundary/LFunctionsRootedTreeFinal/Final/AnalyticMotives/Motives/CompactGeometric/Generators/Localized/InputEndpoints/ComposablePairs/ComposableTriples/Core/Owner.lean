import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.Owner

/-!
# Core composable triples of localization inputs
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A composable triple of localization inputs with two certified middle endpoints. -/
structure TraceLocalizationInputComposableTriple where
  first : TraceLocalizationInput
  second : TraceLocalizationInput
  third : TraceLocalizationInput
  first_middle_eq : first.targetObject = second.sourceObject
  second_middle_eq : second.targetObject = third.sourceObject

/-- The first adjacent composable pair in a composable triple. -/
def TraceLocalizationInputComposableTriple.leftPair
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationInputComposablePair where
  left := triple.first
  right := triple.second
  middle_eq := triple.first_middle_eq

/-- The second adjacent composable pair in a composable triple. -/
def TraceLocalizationInputComposableTriple.rightPair
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationInputComposablePair where
  left := triple.second
  right := triple.third
  middle_eq := triple.second_middle_eq

/-- The first adjacent pair has the first input as left input. -/
theorem TraceLocalizationInputComposableTriple.leftPair_left
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.left =
      triple.first :=
  rfl

/-- The first adjacent pair has the second input as right input. -/
theorem TraceLocalizationInputComposableTriple.leftPair_right
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.right =
      triple.second :=
  rfl

/-- The second adjacent pair has the second input as left input. -/
theorem TraceLocalizationInputComposableTriple.rightPair_left
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.left =
      triple.second :=
  rfl

/-- The second adjacent pair has the third input as right input. -/
theorem TraceLocalizationInputComposableTriple.rightPair_right
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.right =
      triple.third :=
  rfl

/-- The first endpoint equality carried by a composable triple. -/
theorem TraceLocalizationInputComposableTriple.firstMiddleObject_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.targetObject =
      triple.second.sourceObject :=
  triple.first_middle_eq

/-- The second endpoint equality carried by a composable triple. -/
theorem TraceLocalizationInputComposableTriple.secondMiddleObject_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.targetObject =
      triple.third.sourceObject :=
  triple.second_middle_eq

/-- The first adjacent pair remembers the first middle equality. -/
theorem TraceLocalizationInputComposableTriple.leftPair_middle_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middle_eq =
      triple.first_middle_eq :=
  rfl

/-- The second adjacent pair remembers the second middle equality. -/
theorem TraceLocalizationInputComposableTriple.rightPair_middle_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middle_eq =
      triple.second_middle_eq :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
