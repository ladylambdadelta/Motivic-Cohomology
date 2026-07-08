import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.AdjacentPairs.Owner

/-!
# Motive-root adjacent pairs inside composable triples

This file exposes adjacent-pair endpoint projection facts through the
motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the left pair source object is the triple source object. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_sourceObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourceObject =
      triple.sourceObject :=
  TraceLocalizationInputComposableTriple.leftPair_sourceObject
    triple

/-- Motive-root wrapper: the left pair middle object is the first middle object. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_middleObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middleObject =
      triple.firstMiddleObject :=
  TraceLocalizationInputComposableTriple.leftPair_middleObject
    triple

/-- Motive-root wrapper: the left pair target object is the second middle object. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_targetObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetObject =
      triple.secondMiddleObject :=
  TraceLocalizationInputComposableTriple.leftPair_targetObject
    triple

/-- Motive-root wrapper: the right pair source object agrees with the first middle object. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_sourceObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourceObject =
      triple.firstMiddleObject :=
  TraceLocalizationInputComposableTriple.rightPair_sourceObject
    triple

/-- Motive-root wrapper: the right pair middle object is the second middle object. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_middleObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middleObject =
      triple.secondMiddleObject :=
  TraceLocalizationInputComposableTriple.rightPair_middleObject
    triple

/-- Motive-root wrapper: the right pair target object is the triple target object. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_targetObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetObject =
      triple.targetObject :=
  TraceLocalizationInputComposableTriple.rightPair_targetObject
    triple

/-- Motive-root wrapper: the left pair source generator is the triple source generator. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_sourceGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourceGenerator =
      triple.sourceGenerator :=
  TraceLocalizationInputComposableTriple.leftPair_sourceGenerator
    triple

/-- Motive-root wrapper: the left pair middle generator is the first middle generator. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_middleGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middleGenerator =
      triple.firstMiddleGenerator :=
  TraceLocalizationInputComposableTriple.leftPair_middleGenerator
    triple

/-- Motive-root wrapper: the left pair target generator is the second middle generator. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_targetGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetGenerator =
      triple.secondMiddleGenerator :=
  TraceLocalizationInputComposableTriple.leftPair_targetGenerator
    triple

/-- Motive-root wrapper: the right pair source generator agrees with the first middle generator. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_sourceGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourceGenerator =
      triple.firstMiddleGenerator :=
  TraceLocalizationInputComposableTriple.rightPair_sourceGenerator
    triple

/-- Motive-root wrapper: the right pair middle generator is the second middle generator. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_middleGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middleGenerator =
      triple.secondMiddleGenerator :=
  TraceLocalizationInputComposableTriple.rightPair_middleGenerator
    triple

/-- Motive-root wrapper: the right pair target generator is the triple target generator. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_targetGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetGenerator =
      triple.targetGenerator :=
  TraceLocalizationInputComposableTriple.rightPair_targetGenerator
    triple

/-- Motive-root wrapper: the left pair source presheaf is the triple source presheaf. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_sourcePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourcePresheaf =
      triple.sourcePresheaf :=
  TraceLocalizationInputComposableTriple.leftPair_sourcePresheaf
    triple

/-- Motive-root wrapper: the left pair middle presheaf is the first middle presheaf. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_middlePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middlePresheaf =
      triple.firstMiddlePresheaf :=
  TraceLocalizationInputComposableTriple.leftPair_middlePresheaf
    triple

/-- Motive-root wrapper: the left pair target presheaf is the second middle presheaf. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_targetPresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetPresheaf =
      triple.secondMiddlePresheaf :=
  TraceLocalizationInputComposableTriple.leftPair_targetPresheaf
    triple

/-- Motive-root wrapper: the right pair source presheaf agrees with the first middle presheaf. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_sourcePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourcePresheaf =
      triple.firstMiddlePresheaf :=
  TraceLocalizationInputComposableTriple.rightPair_sourcePresheaf
    triple

/-- Motive-root wrapper: the right pair middle presheaf is the second middle presheaf. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_middlePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middlePresheaf =
      triple.secondMiddlePresheaf :=
  TraceLocalizationInputComposableTriple.rightPair_middlePresheaf
    triple

/-- Motive-root wrapper: the right pair target presheaf is the triple target presheaf. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_targetPresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetPresheaf =
      triple.targetPresheaf :=
  TraceLocalizationInputComposableTriple.rightPair_targetPresheaf
    triple

/-- Motive-root wrapper: the left pair source localized object is the triple source. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_sourceLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourceLocalizedObject =
      triple.sourceLocalizedObject :=
  TraceLocalizationInputComposableTriple.leftPair_sourceLocalizedObject
    triple

/-- Motive-root wrapper: the left pair middle localized object is the first middle. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_middleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middleLocalizedObject =
      triple.firstMiddleLocalizedObject :=
  TraceLocalizationInputComposableTriple.leftPair_middleLocalizedObject
    triple

/-- Motive-root wrapper: the left pair target localized object is the second middle. -/
theorem TraceAnalyticMotive.composableTriple_leftPair_targetLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetLocalizedObject =
      triple.secondMiddleLocalizedObject :=
  TraceLocalizationInputComposableTriple.leftPair_targetLocalizedObject
    triple

/-- Motive-root wrapper: the right pair source localized object agrees with the first middle. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_sourceLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourceLocalizedObject =
      triple.firstMiddleLocalizedObject :=
  TraceLocalizationInputComposableTriple.rightPair_sourceLocalizedObject
    triple

/-- Motive-root wrapper: the right pair middle localized object is the second middle. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_middleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middleLocalizedObject =
      triple.secondMiddleLocalizedObject :=
  TraceLocalizationInputComposableTriple.rightPair_middleLocalizedObject
    triple

/-- Motive-root wrapper: the right pair target localized object is the triple target. -/
theorem TraceAnalyticMotive.composableTriple_rightPair_targetLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetLocalizedObject =
      triple.targetLocalizedObject :=
  TraceLocalizationInputComposableTriple.rightPair_targetLocalizedObject
    triple

end AnalyticMotives
end LFunctions
end Boundary
