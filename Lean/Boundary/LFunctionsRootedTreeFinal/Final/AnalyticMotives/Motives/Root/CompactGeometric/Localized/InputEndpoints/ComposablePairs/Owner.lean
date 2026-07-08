import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.ComposedTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.RightTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Owner

/-!
# Motive-root composable localization-input pairs

This file exposes composable localization-input pair endpoint facts through
the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the pair source object is the left source object. -/
theorem TraceAnalyticMotive.composablePair_sourceObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceObject =
      pair.left.sourceObject :=
  TraceLocalizationInputComposablePair.sourceObject_eq_left
    pair

/-- Motive-root wrapper: the pair middle object is the left target object. -/
theorem TraceAnalyticMotive.composablePair_middleObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleObject =
      pair.left.targetObject :=
  TraceLocalizationInputComposablePair.middleObject_eq_left
    pair

/-- Motive-root wrapper: the pair target object is the right target object. -/
theorem TraceAnalyticMotive.composablePair_targetObject_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetObject =
      pair.right.targetObject :=
  TraceLocalizationInputComposablePair.targetObject_eq_right
    pair

/-- Motive-root wrapper: the pair source presheaf is the left source presheaf. -/
theorem TraceAnalyticMotive.composablePair_sourcePresheaf_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourcePresheaf =
      pair.left.sourcePresheaf :=
  TraceLocalizationInputComposablePair.sourcePresheaf_eq_left
    pair

/-- Motive-root wrapper: the pair middle presheaf is the left target presheaf. -/
theorem TraceAnalyticMotive.composablePair_middlePresheaf_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middlePresheaf =
      pair.left.targetPresheaf :=
  TraceLocalizationInputComposablePair.middlePresheaf_eq_left
    pair

/-- Motive-root wrapper: the pair target presheaf is the right target presheaf. -/
theorem TraceAnalyticMotive.composablePair_targetPresheaf_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetPresheaf =
      pair.right.targetPresheaf :=
  TraceLocalizationInputComposablePair.targetPresheaf_eq_right
    pair

/-- Motive-root wrapper: the pair source generator is the left source generator. -/
theorem TraceAnalyticMotive.composablePair_sourceGenerator_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator =
      pair.left.sourceGenerator :=
  TraceLocalizationInputComposablePair.sourceGenerator_eq_left
    pair

/-- Motive-root wrapper: the pair middle generator is the left target generator. -/
theorem TraceAnalyticMotive.composablePair_middleGenerator_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator =
      pair.left.targetGenerator :=
  TraceLocalizationInputComposablePair.middleGenerator_eq_left
    pair

/-- Motive-root wrapper: the pair target generator is the right target generator. -/
theorem TraceAnalyticMotive.composablePair_targetGenerator_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetGenerator =
      pair.right.targetGenerator :=
  TraceLocalizationInputComposablePair.targetGenerator_eq_right
    pair

/-- Motive-root wrapper: the pair source localized object is the left source localized object. -/
theorem TraceAnalyticMotive.composablePair_sourceLocalizedObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceLocalizedObject =
      pair.left.sourceGenerator.localizedObject :=
  TraceLocalizationInputComposablePair.sourceLocalizedObject_eq_left
    pair

/-- Motive-root wrapper: the pair middle localized object is the left target localized object. -/
theorem TraceAnalyticMotive.composablePair_middleLocalizedObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleLocalizedObject =
      pair.left.targetGenerator.localizedObject :=
  TraceLocalizationInputComposablePair.middleLocalizedObject_eq_left
    pair

/-- Motive-root wrapper: the pair target localized object is the right target localized object. -/
theorem TraceAnalyticMotive.composablePair_targetLocalizedObject_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetLocalizedObject =
      pair.right.targetGenerator.localizedObject :=
  TraceLocalizationInputComposablePair.targetLocalizedObject_eq_right
    pair

/-- Motive-root wrapper: the middle trace object equality carried by a composable pair. -/
theorem TraceAnalyticMotive.composablePair_middleObject_eq
    (pair : TraceLocalizationInputComposablePair) :
    pair.left.targetObject =
      pair.right.sourceObject :=
  TraceLocalizationInputComposablePair.middleObject_eq
    pair

/-- Motive-root wrapper: the pair middle object agrees with the right input source. -/
theorem TraceAnalyticMotive.composablePair_middleObject_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleObject =
      pair.right.sourceObject :=
  TraceLocalizationInputComposablePair.middleObject_eq_right_source
    pair

/-- Motive-root wrapper: the pair middle presheaf agrees with the right source presheaf. -/
theorem TraceAnalyticMotive.composablePair_middlePresheaf_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middlePresheaf =
      pair.right.sourcePresheaf :=
  TraceLocalizationInputComposablePair.middlePresheaf_eq_right_source
    pair

/-- Motive-root wrapper: the source generator remembers the pair source object. -/
theorem TraceAnalyticMotive.composablePair_sourceGenerator_traceObject
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator.traceObject =
      pair.sourceObject :=
  TraceLocalizationInputComposablePair.sourceGenerator_traceObject
    pair

/-- Motive-root wrapper: the middle generator remembers the pair middle object. -/
theorem TraceAnalyticMotive.composablePair_middleGenerator_traceObject
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator.traceObject =
      pair.middleObject :=
  TraceLocalizationInputComposablePair.middleGenerator_traceObject
    pair

/-- Motive-root wrapper: the target generator remembers the pair target object. -/
theorem TraceAnalyticMotive.composablePair_targetGenerator_traceObject
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetGenerator.traceObject =
      pair.targetObject :=
  TraceLocalizationInputComposablePair.targetGenerator_traceObject
    pair

/-- Motive-root wrapper: the source generator has the pair source presheaf. -/
theorem TraceAnalyticMotive.composablePair_sourceGenerator_presheaf
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator.presheaf =
      pair.sourcePresheaf :=
  TraceLocalizationInputComposablePair.sourceGenerator_presheaf
    pair

/-- Motive-root wrapper: the middle generator has the pair middle presheaf. -/
theorem TraceAnalyticMotive.composablePair_middleGenerator_presheaf
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator.presheaf =
      pair.middlePresheaf :=
  TraceLocalizationInputComposablePair.middleGenerator_presheaf
    pair

/-- Motive-root wrapper: the target generator has the pair target presheaf. -/
theorem TraceAnalyticMotive.composablePair_targetGenerator_presheaf
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetGenerator.presheaf =
      pair.targetPresheaf :=
  TraceLocalizationInputComposablePair.targetGenerator_presheaf
    pair

/-- Motive-root wrapper: the middle compact-generator endpoints agree. -/
theorem TraceAnalyticMotive.composablePair_middleGenerator_eq
    (pair : TraceLocalizationInputComposablePair) :
    pair.left.targetGenerator =
      pair.right.sourceGenerator :=
  TraceLocalizationInputComposablePair.middleGenerator_eq
    pair

/-- Motive-root wrapper: the reversed middle compact-generator endpoint equality. -/
theorem TraceAnalyticMotive.composablePair_middleGenerator_eq_symm
    (pair : TraceLocalizationInputComposablePair) :
    pair.right.sourceGenerator =
      pair.left.targetGenerator :=
  TraceLocalizationInputComposablePair.middleGenerator_eq_symm
    pair

/-- Motive-root wrapper: the pair middle generator agrees with the right input source. -/
theorem TraceAnalyticMotive.composablePair_middleGenerator_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator =
      pair.right.sourceGenerator :=
  TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
    pair

/-- Motive-root wrapper: the right input source agrees with the pair middle generator. -/
theorem TraceAnalyticMotive.composablePair_right_source_eq_middleGenerator
    (pair : TraceLocalizationInputComposablePair) :
    pair.right.sourceGenerator =
      pair.middleGenerator :=
  TraceLocalizationInputComposablePair.right_source_eq_middleGenerator
    pair

/-- Motive-root wrapper: the source localized object has the pair source object underneath. -/
theorem TraceAnalyticMotive.composablePair_sourceLocalizedObject_underlying
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceLocalizedObject.underlying =
      pair.sourceObject :=
  TraceLocalizationInputComposablePair.sourceLocalizedObject_underlying
    pair

/-- Motive-root wrapper: the middle localized object has the pair middle object underneath. -/
theorem TraceAnalyticMotive.composablePair_middleLocalizedObject_underlying
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleLocalizedObject.underlying =
      pair.middleObject :=
  TraceLocalizationInputComposablePair.middleLocalizedObject_underlying
    pair

/-- Motive-root wrapper: the target localized object has the pair target object underneath. -/
theorem TraceAnalyticMotive.composablePair_targetLocalizedObject_underlying
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetLocalizedObject.underlying =
      pair.targetObject :=
  TraceLocalizationInputComposablePair.targetLocalizedObject_underlying
    pair

/-- Motive-root wrapper: the middle localized object agrees with the right source. -/
theorem TraceAnalyticMotive.composablePair_middleLocalizedObject_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleLocalizedObject =
      pair.right.sourceGenerator.localizedObject :=
  TraceLocalizationInputComposablePair.middleLocalizedObject_eq_right_source
    pair

/-- Motive-root wrapper: the right source localized object agrees with the pair middle. -/
theorem TraceAnalyticMotive.composablePair_right_sourceLocalizedObject_eq_middle
    (pair : TraceLocalizationInputComposablePair) :
    pair.right.sourceGenerator.localizedObject =
      pair.middleLocalizedObject :=
  TraceLocalizationInputComposablePair.right_sourceLocalizedObject_eq_middle
    pair

end AnalyticMotives
end LFunctions
end Boundary
