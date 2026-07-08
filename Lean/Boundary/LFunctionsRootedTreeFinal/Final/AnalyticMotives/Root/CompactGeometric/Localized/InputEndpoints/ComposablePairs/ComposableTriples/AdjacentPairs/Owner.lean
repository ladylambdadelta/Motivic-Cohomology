import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.AdjacentPairs.Owner

/-!
# Public adjacent pairs inside composable triples

This file exposes adjacent-pair endpoint projection facts through the public
analytic-motives root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: the left pair source object is the triple source object. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_sourceObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourceObject =
      triple.sourceObject :=
  TraceAnalyticMotive.composableTriple_leftPair_sourceObject
    triple

/-- Public wrapper: the left pair middle object is the first middle object. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_middleObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middleObject =
      triple.firstMiddleObject :=
  TraceAnalyticMotive.composableTriple_leftPair_middleObject
    triple

/-- Public wrapper: the left pair target object is the second middle object. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_targetObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetObject =
      triple.secondMiddleObject :=
  TraceAnalyticMotive.composableTriple_leftPair_targetObject
    triple

/-- Public wrapper: the right pair source object agrees with the first middle object. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_sourceObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourceObject =
      triple.firstMiddleObject :=
  TraceAnalyticMotive.composableTriple_rightPair_sourceObject
    triple

/-- Public wrapper: the right pair middle object is the second middle object. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_middleObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middleObject =
      triple.secondMiddleObject :=
  TraceAnalyticMotive.composableTriple_rightPair_middleObject
    triple

/-- Public wrapper: the right pair target object is the triple target object. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_targetObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetObject =
      triple.targetObject :=
  TraceAnalyticMotive.composableTriple_rightPair_targetObject
    triple

/-- Public wrapper: the left pair source generator is the triple source generator. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_sourceGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourceGenerator =
      triple.sourceGenerator :=
  TraceAnalyticMotive.composableTriple_leftPair_sourceGenerator
    triple

/-- Public wrapper: the left pair middle generator is the first middle generator. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_middleGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middleGenerator =
      triple.firstMiddleGenerator :=
  TraceAnalyticMotive.composableTriple_leftPair_middleGenerator
    triple

/-- Public wrapper: the left pair target generator is the second middle generator. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_targetGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetGenerator =
      triple.secondMiddleGenerator :=
  TraceAnalyticMotive.composableTriple_leftPair_targetGenerator
    triple

/-- Public wrapper: the right pair source generator agrees with the first middle generator. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_sourceGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourceGenerator =
      triple.firstMiddleGenerator :=
  TraceAnalyticMotive.composableTriple_rightPair_sourceGenerator
    triple

/-- Public wrapper: the right pair middle generator is the second middle generator. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_middleGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middleGenerator =
      triple.secondMiddleGenerator :=
  TraceAnalyticMotive.composableTriple_rightPair_middleGenerator
    triple

/-- Public wrapper: the right pair target generator is the triple target generator. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_targetGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetGenerator =
      triple.targetGenerator :=
  TraceAnalyticMotive.composableTriple_rightPair_targetGenerator
    triple

/-- Public wrapper: the left pair source presheaf is the triple source presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_sourcePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourcePresheaf =
      triple.sourcePresheaf :=
  TraceAnalyticMotive.composableTriple_leftPair_sourcePresheaf
    triple

/-- Public wrapper: the left pair middle presheaf is the first middle presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_middlePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middlePresheaf =
      triple.firstMiddlePresheaf :=
  TraceAnalyticMotive.composableTriple_leftPair_middlePresheaf
    triple

/-- Public wrapper: the left pair target presheaf is the second middle presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_targetPresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetPresheaf =
      triple.secondMiddlePresheaf :=
  TraceAnalyticMotive.composableTriple_leftPair_targetPresheaf
    triple

/-- Public wrapper: the right pair source presheaf agrees with the first middle presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_sourcePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourcePresheaf =
      triple.firstMiddlePresheaf :=
  TraceAnalyticMotive.composableTriple_rightPair_sourcePresheaf
    triple

/-- Public wrapper: the right pair middle presheaf is the second middle presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_middlePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middlePresheaf =
      triple.secondMiddlePresheaf :=
  TraceAnalyticMotive.composableTriple_rightPair_middlePresheaf
    triple

/-- Public wrapper: the right pair target presheaf is the triple target presheaf. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_targetPresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetPresheaf =
      triple.targetPresheaf :=
  TraceAnalyticMotive.composableTriple_rightPair_targetPresheaf
    triple

/-- Public wrapper: the left pair source localized object is the triple source. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_sourceLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourceLocalizedObject =
      triple.sourceLocalizedObject :=
  TraceAnalyticMotive.composableTriple_leftPair_sourceLocalizedObject
    triple

/-- Public wrapper: the left pair middle localized object is the first middle. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_middleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middleLocalizedObject =
      triple.firstMiddleLocalizedObject :=
  TraceAnalyticMotive.composableTriple_leftPair_middleLocalizedObject
    triple

/-- Public wrapper: the left pair target localized object is the second middle. -/
theorem AnalyticMotivesRoot.composableTriple_leftPair_targetLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetLocalizedObject =
      triple.secondMiddleLocalizedObject :=
  TraceAnalyticMotive.composableTriple_leftPair_targetLocalizedObject
    triple

/-- Public wrapper: the right pair source localized object agrees with the first middle. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_sourceLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourceLocalizedObject =
      triple.firstMiddleLocalizedObject :=
  TraceAnalyticMotive.composableTriple_rightPair_sourceLocalizedObject
    triple

/-- Public wrapper: the right pair middle localized object is the second middle. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_middleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middleLocalizedObject =
      triple.secondMiddleLocalizedObject :=
  TraceAnalyticMotive.composableTriple_rightPair_middleLocalizedObject
    triple

/-- Public wrapper: the right pair target localized object is the triple target. -/
theorem AnalyticMotivesRoot.composableTriple_rightPair_targetLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetLocalizedObject =
      triple.targetLocalizedObject :=
  TraceAnalyticMotive.composableTriple_rightPair_targetLocalizedObject
    triple

end AnalyticMotives
end LFunctions
end Boundary
