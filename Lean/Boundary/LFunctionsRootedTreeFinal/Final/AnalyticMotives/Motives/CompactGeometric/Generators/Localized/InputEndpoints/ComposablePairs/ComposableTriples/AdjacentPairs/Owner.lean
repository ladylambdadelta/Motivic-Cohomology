import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Owner

/-!
# Adjacent pairs inside composable triples

This file records how the two adjacent composable pairs of a composable triple
project back to the named triple endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left adjacent pair source object is the triple source object. -/
theorem TraceLocalizationInputComposableTriple.leftPair_sourceObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourceObject =
      triple.sourceObject :=
  rfl

/-- The left adjacent pair middle object is the first middle object. -/
theorem TraceLocalizationInputComposableTriple.leftPair_middleObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middleObject =
      triple.firstMiddleObject :=
  rfl

/-- The left adjacent pair target object is the second middle object. -/
theorem TraceLocalizationInputComposableTriple.leftPair_targetObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetObject =
      triple.secondMiddleObject :=
  rfl

/-- The right adjacent pair source object agrees with the first middle object. -/
theorem TraceLocalizationInputComposableTriple.rightPair_sourceObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourceObject =
      triple.firstMiddleObject :=
  Eq.symm
    (TraceLocalizationInputComposableTriple.firstMiddleObject_eq_second_source
      triple)

/-- The right adjacent pair middle object is the second middle object. -/
theorem TraceLocalizationInputComposableTriple.rightPair_middleObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middleObject =
      triple.secondMiddleObject :=
  rfl

/-- The right adjacent pair target object is the triple target object. -/
theorem TraceLocalizationInputComposableTriple.rightPair_targetObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetObject =
      triple.targetObject :=
  rfl

/-- The left adjacent pair source generator is the triple source generator. -/
theorem TraceLocalizationInputComposableTriple.leftPair_sourceGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourceGenerator =
      triple.sourceGenerator :=
  rfl

/-- The left adjacent pair middle generator is the first middle generator. -/
theorem TraceLocalizationInputComposableTriple.leftPair_middleGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middleGenerator =
      triple.firstMiddleGenerator :=
  rfl

/-- The left adjacent pair target generator is the second middle generator. -/
theorem TraceLocalizationInputComposableTriple.leftPair_targetGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetGenerator =
      triple.secondMiddleGenerator :=
  rfl

/-- The right adjacent pair source generator agrees with the first middle generator. -/
theorem TraceLocalizationInputComposableTriple.rightPair_sourceGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourceGenerator =
      triple.firstMiddleGenerator :=
  Eq.symm
    (TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
      triple)

/-- The right adjacent pair middle generator is the second middle generator. -/
theorem TraceLocalizationInputComposableTriple.rightPair_middleGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middleGenerator =
      triple.secondMiddleGenerator :=
  rfl

/-- The right adjacent pair target generator is the triple target generator. -/
theorem TraceLocalizationInputComposableTriple.rightPair_targetGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetGenerator =
      triple.targetGenerator :=
  rfl

/-- The left adjacent pair source presheaf is the triple source presheaf. -/
theorem TraceLocalizationInputComposableTriple.leftPair_sourcePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourcePresheaf =
      triple.sourcePresheaf :=
  rfl

/-- The left adjacent pair middle presheaf is the first middle presheaf. -/
theorem TraceLocalizationInputComposableTriple.leftPair_middlePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middlePresheaf =
      triple.firstMiddlePresheaf :=
  rfl

/-- The left adjacent pair target presheaf is the second middle presheaf. -/
theorem TraceLocalizationInputComposableTriple.leftPair_targetPresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetPresheaf =
      triple.secondMiddlePresheaf :=
  rfl

/-- The right adjacent pair source presheaf agrees with the first middle presheaf. -/
theorem TraceLocalizationInputComposableTriple.rightPair_sourcePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourcePresheaf =
      triple.firstMiddlePresheaf :=
  Eq.symm
    (TraceLocalizationInputComposableTriple.firstMiddlePresheaf_eq_second_source
      triple)

/-- The right adjacent pair middle presheaf is the second middle presheaf. -/
theorem TraceLocalizationInputComposableTriple.rightPair_middlePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middlePresheaf =
      triple.secondMiddlePresheaf :=
  rfl

/-- The right adjacent pair target presheaf is the triple target presheaf. -/
theorem TraceLocalizationInputComposableTriple.rightPair_targetPresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetPresheaf =
      triple.targetPresheaf :=
  rfl

/-- The left adjacent pair source localized object is the triple source localized object. -/
theorem TraceLocalizationInputComposableTriple.leftPair_sourceLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.sourceLocalizedObject =
      triple.sourceLocalizedObject :=
  rfl

/-- The left adjacent pair middle localized object is the first middle localized object. -/
theorem TraceLocalizationInputComposableTriple.leftPair_middleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.middleLocalizedObject =
      triple.firstMiddleLocalizedObject :=
  rfl

/-- The left adjacent pair target localized object is the second middle localized object. -/
theorem TraceLocalizationInputComposableTriple.leftPair_targetLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.targetLocalizedObject =
      triple.secondMiddleLocalizedObject :=
  rfl

/-- The right adjacent pair source localized object agrees with the first middle localized object. -/
theorem TraceLocalizationInputComposableTriple.rightPair_sourceLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.sourceLocalizedObject =
      triple.firstMiddleLocalizedObject :=
  Eq.symm
    (TraceLocalizationInputComposableTriple.firstMiddleLocalizedObject_eq_second_source
      triple)

/-- The right adjacent pair middle localized object is the second middle localized object. -/
theorem TraceLocalizationInputComposableTriple.rightPair_middleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.middleLocalizedObject =
      triple.secondMiddleLocalizedObject :=
  rfl

/-- The right adjacent pair target localized object is the triple target localized object. -/
theorem TraceLocalizationInputComposableTriple.rightPair_targetLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.targetLocalizedObject =
      triple.targetLocalizedObject :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
