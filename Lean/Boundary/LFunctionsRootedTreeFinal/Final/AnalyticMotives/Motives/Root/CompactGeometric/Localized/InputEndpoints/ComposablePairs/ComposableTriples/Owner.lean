import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.AdjacentPairs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.AdjacentCompositeTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.InputFactors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.ThreeInputAssociativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.ThreeInputFormulas.Owner

/-!
# Motive-root composable triples of localization inputs

This file exposes composable-triple endpoint facts through the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the first adjacent pair has the first input as left input. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_left
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.left =
      triple.first :=
  TraceLocalizationInputComposableTriple.leftPair_left
    triple

/-- Motive-root wrapper: the first adjacent pair has the second input as right input. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_right
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.right =
      triple.second :=
  TraceLocalizationInputComposableTriple.leftPair_right
    triple

/-- Motive-root wrapper: the second adjacent pair has the second input as left input. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_left
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.left =
      triple.second :=
  TraceLocalizationInputComposableTriple.rightPair_left
    triple

/-- Motive-root wrapper: the second adjacent pair has the third input as right input. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_right
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.right =
      triple.third :=
  TraceLocalizationInputComposableTriple.rightPair_right
    triple

/-- Motive-root wrapper: the first endpoint equality carried by a composable triple. -/
theorem TraceAnalyticMotive.composableTriple_firstMiddleObject_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.targetObject =
      triple.second.sourceObject :=
  TraceLocalizationInputComposableTriple.firstMiddleObject_eq
    triple

/-- Motive-root wrapper: the second endpoint equality carried by a composable triple. -/
theorem TraceAnalyticMotive.composableTriple_secondMiddleObject_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.targetObject =
      triple.third.sourceObject :=
  TraceLocalizationInputComposableTriple.secondMiddleObject_eq
    triple

/-- Motive-root wrapper: the triple source object is the first source object. -/
theorem TraceAnalyticMotive.composableTriple_sourceObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceObject =
      triple.first.sourceObject :=
  TraceLocalizationInputComposableTriple.sourceObject_eq_first
    triple

/-- Motive-root wrapper: the first middle object is the first target object. -/
theorem TraceAnalyticMotive.composableTriple_firstMiddleObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleObject =
      triple.first.targetObject :=
  TraceLocalizationInputComposableTriple.firstMiddleObject_eq_first
    triple

/-- Motive-root wrapper: the second middle object is the second target object. -/
theorem TraceAnalyticMotive.composableTriple_secondMiddleObject_eq_second
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleObject =
      triple.second.targetObject :=
  TraceLocalizationInputComposableTriple.secondMiddleObject_eq_second
    triple

/-- Motive-root wrapper: the triple target object is the third target object. -/
theorem TraceAnalyticMotive.composableTriple_targetObject_eq_third
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetObject =
      triple.third.targetObject :=
  TraceLocalizationInputComposableTriple.targetObject_eq_third
    triple

/-- Motive-root wrapper: the first middle object agrees with the second source. -/
theorem TraceAnalyticMotive.composableTriple_firstMiddleObject_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleObject =
      triple.second.sourceObject :=
  TraceLocalizationInputComposableTriple.firstMiddleObject_eq_second_source
    triple

/-- Motive-root wrapper: the second middle object agrees with the third source. -/
theorem TraceAnalyticMotive.composableTriple_secondMiddleObject_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleObject =
      triple.third.sourceObject :=
  TraceLocalizationInputComposableTriple.secondMiddleObject_eq_third_source
    triple

/-- Motive-root wrapper: the first middle generator agrees with the second source. -/
theorem TraceAnalyticMotive.composableTriple_firstMiddleGenerator_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleGenerator =
      triple.second.sourceGenerator :=
  TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
    triple

/-- Motive-root wrapper: the second middle generator agrees with the third source. -/
theorem TraceAnalyticMotive.composableTriple_secondMiddleGenerator_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleGenerator =
      triple.third.sourceGenerator :=
  TraceLocalizationInputComposableTriple.secondMiddleGenerator_eq_third_source
    triple

/-- Motive-root wrapper: the triple source presheaf is the first source presheaf. -/
theorem TraceAnalyticMotive.composableTriple_sourcePresheaf_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourcePresheaf =
      triple.first.sourcePresheaf :=
  TraceLocalizationInputComposableTriple.sourcePresheaf_eq_first
    triple

/-- Motive-root wrapper: the first middle presheaf is the first target presheaf. -/
theorem TraceAnalyticMotive.composableTriple_firstMiddlePresheaf_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddlePresheaf =
      triple.first.targetPresheaf :=
  TraceLocalizationInputComposableTriple.firstMiddlePresheaf_eq_first
    triple

/-- Motive-root wrapper: the second middle presheaf is the second target presheaf. -/
theorem TraceAnalyticMotive.composableTriple_secondMiddlePresheaf_eq_second
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddlePresheaf =
      triple.second.targetPresheaf :=
  TraceLocalizationInputComposableTriple.secondMiddlePresheaf_eq_second
    triple

/-- Motive-root wrapper: the triple target presheaf is the third target presheaf. -/
theorem TraceAnalyticMotive.composableTriple_targetPresheaf_eq_third
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetPresheaf =
      triple.third.targetPresheaf :=
  TraceLocalizationInputComposableTriple.targetPresheaf_eq_third
    triple

/-- Motive-root wrapper: the first middle presheaf agrees with the second source. -/
theorem TraceAnalyticMotive.composableTriple_firstMiddlePresheaf_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddlePresheaf =
      triple.second.sourcePresheaf :=
  TraceLocalizationInputComposableTriple.firstMiddlePresheaf_eq_second_source
    triple

/-- Motive-root wrapper: the second middle presheaf agrees with the third source. -/
theorem TraceAnalyticMotive.composableTriple_secondMiddlePresheaf_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddlePresheaf =
      triple.third.sourcePresheaf :=
  TraceLocalizationInputComposableTriple.secondMiddlePresheaf_eq_third_source
    triple

/-- Motive-root wrapper: the source generator has the triple source presheaf. -/
theorem TraceAnalyticMotive.composableTriple_sourceGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceGenerator.presheaf =
      triple.sourcePresheaf :=
  TraceLocalizationInputComposableTriple.sourceGenerator_presheaf
    triple

/-- Motive-root wrapper: the first middle generator has the first middle presheaf. -/
theorem TraceAnalyticMotive.composableTriple_firstMiddleGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleGenerator.presheaf =
      triple.firstMiddlePresheaf :=
  TraceLocalizationInputComposableTriple.firstMiddleGenerator_presheaf
    triple

/-- Motive-root wrapper: the second middle generator has the second middle presheaf. -/
theorem TraceAnalyticMotive.composableTriple_secondMiddleGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleGenerator.presheaf =
      triple.secondMiddlePresheaf :=
  TraceLocalizationInputComposableTriple.secondMiddleGenerator_presheaf
    triple

/-- Motive-root wrapper: the target generator has the triple target presheaf. -/
theorem TraceAnalyticMotive.composableTriple_targetGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetGenerator.presheaf =
      triple.targetPresheaf :=
  TraceLocalizationInputComposableTriple.targetGenerator_presheaf
    triple

/-- Motive-root wrapper: the triple source localized object is the first source localized object. -/
theorem TraceAnalyticMotive.composableTriple_sourceLocalizedObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceLocalizedObject =
      triple.first.sourceGenerator.localizedObject :=
  TraceLocalizationInputComposableTriple.sourceLocalizedObject_eq_first
    triple

/-- Motive-root wrapper: the first middle localized object is the first target localized object. -/
theorem TraceAnalyticMotive.composableTriple_firstMiddleLocalizedObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleLocalizedObject =
      triple.first.targetGenerator.localizedObject :=
  TraceLocalizationInputComposableTriple.firstMiddleLocalizedObject_eq_first
    triple

/-- Motive-root wrapper: the second middle localized object is the second target localized object. -/
theorem TraceAnalyticMotive.composableTriple_secondMiddleLocalizedObject_eq_second
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleLocalizedObject =
      triple.second.targetGenerator.localizedObject :=
  TraceLocalizationInputComposableTriple.secondMiddleLocalizedObject_eq_second
    triple

/-- Motive-root wrapper: the triple target localized object is the third target localized object. -/
theorem TraceAnalyticMotive.composableTriple_targetLocalizedObject_eq_third
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetLocalizedObject =
      triple.third.targetGenerator.localizedObject :=
  TraceLocalizationInputComposableTriple.targetLocalizedObject_eq_third
    triple

/-- Motive-root wrapper: the source localized object has the first source underneath. -/
theorem TraceAnalyticMotive.composableTriple_sourceLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceLocalizedObject.underlying =
      triple.sourceObject :=
  TraceLocalizationInputComposableTriple.sourceLocalizedObject_underlying
    triple

/-- Motive-root wrapper: the first middle localized object has the first target underneath. -/
theorem TraceAnalyticMotive.composableTriple_firstMiddleLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleLocalizedObject.underlying =
      triple.firstMiddleObject :=
  TraceLocalizationInputComposableTriple.firstMiddleLocalizedObject_underlying
    triple

/-- Motive-root wrapper: the second middle localized object has the second target underneath. -/
theorem TraceAnalyticMotive.composableTriple_secondMiddleLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleLocalizedObject.underlying =
      triple.secondMiddleObject :=
  TraceLocalizationInputComposableTriple.secondMiddleLocalizedObject_underlying
    triple

/-- Motive-root wrapper: the target localized object has the third target underneath. -/
theorem TraceAnalyticMotive.composableTriple_targetLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetLocalizedObject.underlying =
      triple.targetObject :=
  TraceLocalizationInputComposableTriple.targetLocalizedObject_underlying
    triple

/-- Motive-root wrapper: the first middle localized object agrees with the second source. -/
theorem TraceAnalyticMotive.composableTriple_firstMiddleLocalizedObject_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleLocalizedObject =
      triple.second.sourceGenerator.localizedObject :=
  TraceLocalizationInputComposableTriple.firstMiddleLocalizedObject_eq_second_source
    triple

/-- Motive-root wrapper: the second middle localized object agrees with the third source. -/
theorem TraceAnalyticMotive.composableTriple_secondMiddleLocalizedObject_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleLocalizedObject =
      triple.third.sourceGenerator.localizedObject :=
  TraceLocalizationInputComposableTriple.secondMiddleLocalizedObject_eq_third_source
    triple

end AnalyticMotives
end LFunctions
end Boundary
