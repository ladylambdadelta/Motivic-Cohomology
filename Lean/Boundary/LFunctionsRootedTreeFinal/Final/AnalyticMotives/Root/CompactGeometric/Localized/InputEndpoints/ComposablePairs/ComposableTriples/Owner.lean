import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.AdjacentPairs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.AdjacentCompositeTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.InputFactors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.ThreeInputAssociativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.ThreeInputFormulas.Owner

/-!
# Public composable triples of localization inputs

This file exposes composable-triple endpoint facts through the public
analytic-motives root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: the first adjacent pair has the first input as left input. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_left
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.left =
      triple.first :=
  TraceAnalyticMotive.composableTriple_leftPair_left
    triple

/-- Public wrapper: the first adjacent pair has the second input as right input. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_right
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.right =
      triple.second :=
  TraceAnalyticMotive.composableTriple_leftPair_right
    triple

/-- Public wrapper: the second adjacent pair has the second input as left input. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_left
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.left =
      triple.second :=
  TraceAnalyticMotive.composableTriple_rightPair_left
    triple

/-- Public wrapper: the second adjacent pair has the third input as right input. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_right
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.right =
      triple.third :=
  TraceAnalyticMotive.composableTriple_rightPair_right
    triple

/-- Public wrapper: the first endpoint equality carried by a composable triple. -/
theorem AnalyticMotivesRoot.composableTriple_firstMiddleObject_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.targetObject =
      triple.second.sourceObject :=
  TraceAnalyticMotive.composableTriple_firstMiddleObject_eq
    triple

/-- Public wrapper: the second endpoint equality carried by a composable triple. -/
theorem AnalyticMotivesRoot.composableTriple_secondMiddleObject_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.targetObject =
      triple.third.sourceObject :=
  TraceAnalyticMotive.composableTriple_secondMiddleObject_eq
    triple

/-- Public wrapper: the triple source object is the first source object. -/
theorem AnalyticMotivesRoot.composableTriple_sourceObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceObject =
      triple.first.sourceObject :=
  TraceAnalyticMotive.composableTriple_sourceObject_eq_first
    triple

/-- Public wrapper: the first middle object is the first target object. -/
theorem AnalyticMotivesRoot.composableTriple_firstMiddleObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleObject =
      triple.first.targetObject :=
  TraceAnalyticMotive.composableTriple_firstMiddleObject_eq_first
    triple

/-- Public wrapper: the second middle object is the second target object. -/
theorem AnalyticMotivesRoot.composableTriple_secondMiddleObject_eq_second
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleObject =
      triple.second.targetObject :=
  TraceAnalyticMotive.composableTriple_secondMiddleObject_eq_second
    triple

/-- Public wrapper: the triple target object is the third target object. -/
theorem AnalyticMotivesRoot.composableTriple_targetObject_eq_third
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetObject =
      triple.third.targetObject :=
  TraceAnalyticMotive.composableTriple_targetObject_eq_third
    triple

/-- Public wrapper: the first middle object agrees with the second source. -/
theorem AnalyticMotivesRoot.composableTriple_firstMiddleObject_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleObject =
      triple.second.sourceObject :=
  TraceAnalyticMotive.composableTriple_firstMiddleObject_eq_second_source
    triple

/-- Public wrapper: the second middle object agrees with the third source. -/
theorem AnalyticMotivesRoot.composableTriple_secondMiddleObject_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleObject =
      triple.third.sourceObject :=
  TraceAnalyticMotive.composableTriple_secondMiddleObject_eq_third_source
    triple

/-- Public wrapper: the first middle generator agrees with the second source. -/
theorem AnalyticMotivesRoot.composableTriple_firstMiddleGenerator_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleGenerator =
      triple.second.sourceGenerator :=
  TraceAnalyticMotive.composableTriple_firstMiddleGenerator_eq_second_source
    triple

/-- Public wrapper: the second middle generator agrees with the third source. -/
theorem AnalyticMotivesRoot.composableTriple_secondMiddleGenerator_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleGenerator =
      triple.third.sourceGenerator :=
  TraceAnalyticMotive.composableTriple_secondMiddleGenerator_eq_third_source
    triple

/-- Public wrapper: the triple source presheaf is the first source presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_sourcePresheaf_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourcePresheaf =
      triple.first.sourcePresheaf :=
  TraceAnalyticMotive.composableTriple_sourcePresheaf_eq_first
    triple

/-- Public wrapper: the first middle presheaf is the first target presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_firstMiddlePresheaf_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddlePresheaf =
      triple.first.targetPresheaf :=
  TraceAnalyticMotive.composableTriple_firstMiddlePresheaf_eq_first
    triple

/-- Public wrapper: the second middle presheaf is the second target presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_secondMiddlePresheaf_eq_second
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddlePresheaf =
      triple.second.targetPresheaf :=
  TraceAnalyticMotive.composableTriple_secondMiddlePresheaf_eq_second
    triple

/-- Public wrapper: the triple target presheaf is the third target presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_targetPresheaf_eq_third
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetPresheaf =
      triple.third.targetPresheaf :=
  TraceAnalyticMotive.composableTriple_targetPresheaf_eq_third
    triple

/-- Public wrapper: the first middle presheaf agrees with the second source. -/
theorem AnalyticMotivesRoot.composableTriple_firstMiddlePresheaf_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddlePresheaf =
      triple.second.sourcePresheaf :=
  TraceAnalyticMotive.composableTriple_firstMiddlePresheaf_eq_second_source
    triple

/-- Public wrapper: the second middle presheaf agrees with the third source. -/
theorem AnalyticMotivesRoot.composableTriple_secondMiddlePresheaf_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddlePresheaf =
      triple.third.sourcePresheaf :=
  TraceAnalyticMotive.composableTriple_secondMiddlePresheaf_eq_third_source
    triple

/-- Public wrapper: the source generator has the triple source presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_sourceGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceGenerator.presheaf =
      triple.sourcePresheaf :=
  TraceAnalyticMotive.composableTriple_sourceGenerator_presheaf
    triple

/-- Public wrapper: the first middle generator has the first middle presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_firstMiddleGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleGenerator.presheaf =
      triple.firstMiddlePresheaf :=
  TraceAnalyticMotive.composableTriple_firstMiddleGenerator_presheaf
    triple

/-- Public wrapper: the second middle generator has the second middle presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_secondMiddleGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleGenerator.presheaf =
      triple.secondMiddlePresheaf :=
  TraceAnalyticMotive.composableTriple_secondMiddleGenerator_presheaf
    triple

/-- Public wrapper: the target generator has the triple target presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_targetGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetGenerator.presheaf =
      triple.targetPresheaf :=
  TraceAnalyticMotive.composableTriple_targetGenerator_presheaf
    triple

/-- Public wrapper: the triple source localized object is the first source localized object. -/
theorem AnalyticMotivesRoot.composableTriple_sourceLocalizedObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceLocalizedObject =
      triple.first.sourceGenerator.localizedObject :=
  TraceAnalyticMotive.composableTriple_sourceLocalizedObject_eq_first
    triple

/-- Public wrapper: the first middle localized object is the first target localized object. -/
theorem AnalyticMotivesRoot.composableTriple_firstMiddleLocalizedObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleLocalizedObject =
      triple.first.targetGenerator.localizedObject :=
  TraceAnalyticMotive.composableTriple_firstMiddleLocalizedObject_eq_first
    triple

/-- Public wrapper: the second middle localized object is the second target localized object. -/
theorem AnalyticMotivesRoot.composableTriple_secondMiddleLocalizedObject_eq_second
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleLocalizedObject =
      triple.second.targetGenerator.localizedObject :=
  TraceAnalyticMotive.composableTriple_secondMiddleLocalizedObject_eq_second
    triple

/-- Public wrapper: the triple target localized object is the third target localized object. -/
theorem AnalyticMotivesRoot.composableTriple_targetLocalizedObject_eq_third
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetLocalizedObject =
      triple.third.targetGenerator.localizedObject :=
  TraceAnalyticMotive.composableTriple_targetLocalizedObject_eq_third
    triple

/-- Public wrapper: the source localized object has the first source underneath. -/
theorem AnalyticMotivesRoot.composableTriple_sourceLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceLocalizedObject.underlying =
      triple.sourceObject :=
  TraceAnalyticMotive.composableTriple_sourceLocalizedObject_underlying
    triple

/-- Public wrapper: the first middle localized object has the first target underneath. -/
theorem AnalyticMotivesRoot.composableTriple_firstMiddleLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleLocalizedObject.underlying =
      triple.firstMiddleObject :=
  TraceAnalyticMotive.composableTriple_firstMiddleLocalizedObject_underlying
    triple

/-- Public wrapper: the second middle localized object has the second target underneath. -/
theorem AnalyticMotivesRoot.composableTriple_secondMiddleLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleLocalizedObject.underlying =
      triple.secondMiddleObject :=
  TraceAnalyticMotive.composableTriple_secondMiddleLocalizedObject_underlying
    triple

/-- Public wrapper: the target localized object has the third target underneath. -/
theorem AnalyticMotivesRoot.composableTriple_targetLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetLocalizedObject.underlying =
      triple.targetObject :=
  TraceAnalyticMotive.composableTriple_targetLocalizedObject_underlying
    triple

/-- Public wrapper: the first middle localized object agrees with the second source. -/
theorem AnalyticMotivesRoot.composableTriple_firstMiddleLocalizedObject_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleLocalizedObject =
      triple.second.sourceGenerator.localizedObject :=
  TraceAnalyticMotive.composableTriple_firstMiddleLocalizedObject_eq_second_source
    triple

/-- Public wrapper: the second middle localized object agrees with the third source. -/
theorem AnalyticMotivesRoot.composableTriple_secondMiddleLocalizedObject_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleLocalizedObject =
      triple.third.sourceGenerator.localizedObject :=
  TraceAnalyticMotive.composableTriple_secondMiddleLocalizedObject_eq_third_source
    triple

end AnalyticMotives
end LFunctions
end Boundary
