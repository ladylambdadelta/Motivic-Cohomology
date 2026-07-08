import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.EndpointTransport.Owner

/-!
# Composable localization-input pairs

This file packages the concrete endpoint equality needed for two localization
inputs to be composable at the compact-generator endpoint level.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A composable pair of localization inputs with a certified middle endpoint equality. -/
structure TraceLocalizationInputComposablePair where
  left : TraceLocalizationInput
  right : TraceLocalizationInput
  middle_eq : left.targetObject = right.sourceObject

/-- The source trace object of a composable pair. -/
def TraceLocalizationInputComposablePair.sourceObject
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQObject :=
  pair.left.sourceObject

/-- The middle trace object of a composable pair, using the left target endpoint. -/
def TraceLocalizationInputComposablePair.middleObject
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQObject :=
  pair.left.targetObject

/-- The target trace object of a composable pair. -/
def TraceLocalizationInputComposablePair.targetObject
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQObject :=
  pair.right.targetObject

/-- The source representable presheaf of a composable pair. -/
def TraceLocalizationInputComposablePair.sourcePresheaf
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQPresheaf :=
  pair.left.sourcePresheaf

/-- The middle representable presheaf of a composable pair, using the left target endpoint. -/
def TraceLocalizationInputComposablePair.middlePresheaf
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQPresheaf :=
  pair.left.targetPresheaf

/-- The target representable presheaf of a composable pair. -/
def TraceLocalizationInputComposablePair.targetPresheaf
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQPresheaf :=
  pair.right.targetPresheaf

/-- The source compact generator of a composable pair. -/
def TraceLocalizationInputComposablePair.sourceGenerator
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator :=
  pair.left.sourceGenerator

/-- The middle compact generator of a composable pair, using the left target endpoint. -/
def TraceLocalizationInputComposablePair.middleGenerator
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator :=
  pair.left.targetGenerator

/-- The target compact generator of a composable pair. -/
def TraceLocalizationInputComposablePair.targetGenerator
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator :=
  pair.right.targetGenerator

/-- The source localized-word object of a composable pair. -/
def TraceLocalizationInputComposablePair.sourceLocalizedObject
    (pair : TraceLocalizationInputComposablePair) :
    TraceLocalizedWordObject :=
  pair.sourceGenerator.localizedObject

/-- The middle localized-word object of a composable pair. -/
def TraceLocalizationInputComposablePair.middleLocalizedObject
    (pair : TraceLocalizationInputComposablePair) :
    TraceLocalizedWordObject :=
  pair.middleGenerator.localizedObject

/-- The target localized-word object of a composable pair. -/
def TraceLocalizationInputComposablePair.targetLocalizedObject
    (pair : TraceLocalizationInputComposablePair) :
    TraceLocalizedWordObject :=
  pair.targetGenerator.localizedObject

/-- The pair source generator is the left input source generator. -/
theorem TraceLocalizationInputComposablePair.sourceGenerator_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator =
      pair.left.sourceGenerator :=
  rfl

/-- The pair source object is the left input source object. -/
theorem TraceLocalizationInputComposablePair.sourceObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceObject =
      pair.left.sourceObject :=
  rfl

/-- The pair middle object is the left input target object. -/
theorem TraceLocalizationInputComposablePair.middleObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleObject =
      pair.left.targetObject :=
  rfl

/-- The pair target object is the right input target object. -/
theorem TraceLocalizationInputComposablePair.targetObject_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetObject =
      pair.right.targetObject :=
  rfl

/-- The pair source presheaf is the left input source presheaf. -/
theorem TraceLocalizationInputComposablePair.sourcePresheaf_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourcePresheaf =
      pair.left.sourcePresheaf :=
  rfl

/-- The pair middle presheaf is the left input target presheaf. -/
theorem TraceLocalizationInputComposablePair.middlePresheaf_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middlePresheaf =
      pair.left.targetPresheaf :=
  rfl

/-- The pair target presheaf is the right input target presheaf. -/
theorem TraceLocalizationInputComposablePair.targetPresheaf_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetPresheaf =
      pair.right.targetPresheaf :=
  rfl

/-- The pair middle generator is the left input target generator. -/
theorem TraceLocalizationInputComposablePair.middleGenerator_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator =
      pair.left.targetGenerator :=
  rfl

/-- The pair target generator is the right input target generator. -/
theorem TraceLocalizationInputComposablePair.targetGenerator_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetGenerator =
      pair.right.targetGenerator :=
  rfl

/-- The pair source localized object is the localized object of the left source generator. -/
theorem TraceLocalizationInputComposablePair.sourceLocalizedObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceLocalizedObject =
      pair.left.sourceGenerator.localizedObject :=
  rfl

/-- The pair middle localized object is the localized object of the left target generator. -/
theorem TraceLocalizationInputComposablePair.middleLocalizedObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleLocalizedObject =
      pair.left.targetGenerator.localizedObject :=
  rfl

/-- The pair target localized object is the localized object of the right target generator. -/
theorem TraceLocalizationInputComposablePair.targetLocalizedObject_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetLocalizedObject =
      pair.right.targetGenerator.localizedObject :=
  rfl

/-- The middle trace object equality carried by a composable pair. -/
theorem TraceLocalizationInputComposablePair.middleObject_eq
    (pair : TraceLocalizationInputComposablePair) :
    pair.left.targetObject =
      pair.right.sourceObject :=
  pair.middle_eq

/-- The pair middle object agrees with the right input source object. -/
theorem TraceLocalizationInputComposablePair.middleObject_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleObject =
      pair.right.sourceObject :=
  Eq.trans
    (TraceLocalizationInputComposablePair.middleObject_eq_left pair)
    (TraceLocalizationInputComposablePair.middleObject_eq pair)

/-- The pair middle presheaf agrees with the right input source presheaf. -/
theorem TraceLocalizationInputComposablePair.middlePresheaf_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middlePresheaf =
      pair.right.sourcePresheaf :=
  congrArg
    TraceCorQPresheaf.representable
    (TraceLocalizationInputComposablePair.middleObject_eq_right_source pair)

/-- The source generator remembers the pair source object. -/
theorem TraceLocalizationInputComposablePair.sourceGenerator_traceObject
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator.traceObject =
      pair.sourceObject :=
  rfl

/-- The middle generator remembers the pair middle object. -/
theorem TraceLocalizationInputComposablePair.middleGenerator_traceObject
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator.traceObject =
      pair.middleObject :=
  rfl

/-- The target generator remembers the pair target object. -/
theorem TraceLocalizationInputComposablePair.targetGenerator_traceObject
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetGenerator.traceObject =
      pair.targetObject :=
  rfl

/-- The source generator has the pair source presheaf. -/
theorem TraceLocalizationInputComposablePair.sourceGenerator_presheaf
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator.presheaf =
      pair.sourcePresheaf :=
  rfl

/-- The middle generator has the pair middle presheaf. -/
theorem TraceLocalizationInputComposablePair.middleGenerator_presheaf
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator.presheaf =
      pair.middlePresheaf :=
  rfl

/-- The target generator has the pair target presheaf. -/
theorem TraceLocalizationInputComposablePair.targetGenerator_presheaf
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetGenerator.presheaf =
      pair.targetPresheaf :=
  rfl

/-- The middle compact-generator endpoints of a composable pair agree. -/
theorem TraceLocalizationInputComposablePair.middleGenerator_eq
    (pair : TraceLocalizationInputComposablePair) :
    pair.left.targetGenerator =
      pair.right.sourceGenerator :=
  TraceLocalizationInput.targetGenerator_eq_sourceGenerator_of_targetObject_eq_sourceObject
    pair.left
    pair.right
    pair.middle_eq

/-- The reversed middle compact-generator equality of a composable pair. -/
theorem TraceLocalizationInputComposablePair.middleGenerator_eq_symm
    (pair : TraceLocalizationInputComposablePair) :
    pair.right.sourceGenerator =
      pair.left.targetGenerator :=
  Eq.symm
    (TraceLocalizationInputComposablePair.middleGenerator_eq pair)

/-- The pair middle generator agrees with the right input source generator. -/
theorem TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator =
      pair.right.sourceGenerator :=
  Eq.trans
    (TraceLocalizationInputComposablePair.middleGenerator_eq_left pair)
    (TraceLocalizationInputComposablePair.middleGenerator_eq pair)

/-- The right input source generator agrees with the pair middle generator. -/
theorem TraceLocalizationInputComposablePair.right_source_eq_middleGenerator
    (pair : TraceLocalizationInputComposablePair) :
    pair.right.sourceGenerator =
      pair.middleGenerator :=
  Eq.symm
    (TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair)

/-- The pair source localized object has the pair source trace object as underlying object. -/
theorem TraceLocalizationInputComposablePair.sourceLocalizedObject_underlying
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceLocalizedObject.underlying =
      pair.sourceObject :=
  rfl

/-- The pair middle localized object has the pair middle trace object as underlying object. -/
theorem TraceLocalizationInputComposablePair.middleLocalizedObject_underlying
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleLocalizedObject.underlying =
      pair.middleObject :=
  rfl

/-- The pair target localized object has the pair target trace object as underlying object. -/
theorem TraceLocalizationInputComposablePair.targetLocalizedObject_underlying
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetLocalizedObject.underlying =
      pair.targetObject :=
  rfl

/-- The pair middle localized object agrees with the right input source localized object. -/
theorem TraceLocalizationInputComposablePair.middleLocalizedObject_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleLocalizedObject =
      pair.right.sourceGenerator.localizedObject :=
  congrArg
    TraceAnalyticGeometricGenerator.localizedObject
    (TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair)

/-- The right input source localized object agrees with the pair middle localized object. -/
theorem TraceLocalizationInputComposablePair.right_sourceLocalizedObject_eq_middle
    (pair : TraceLocalizationInputComposablePair) :
    pair.right.sourceGenerator.localizedObject =
      pair.middleLocalizedObject :=
  Eq.symm
    (TraceLocalizationInputComposablePair.middleLocalizedObject_eq_right_source pair)

end AnalyticMotives
end LFunctions
end Boundary
