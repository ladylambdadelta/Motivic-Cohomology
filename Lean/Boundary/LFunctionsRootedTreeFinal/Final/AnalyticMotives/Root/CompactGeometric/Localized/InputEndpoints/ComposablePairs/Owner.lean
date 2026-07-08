import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.ComposedTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.RightTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Owner

/-!
# Public composable localization-input pairs

This file exposes composable localization-input pair endpoint facts through
the public analytic-motives root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: the pair source object is the left source object. -/
theorem AnalyticMotivesRoot.composablePair_sourceObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceObject =
      pair.left.sourceObject :=
  TraceAnalyticMotive.composablePair_sourceObject_eq_left
    pair

/-- Public wrapper: the pair middle object is the left target object. -/
theorem AnalyticMotivesRoot.composablePair_middleObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleObject =
      pair.left.targetObject :=
  TraceAnalyticMotive.composablePair_middleObject_eq_left
    pair

/-- Public wrapper: the pair target object is the right target object. -/
theorem AnalyticMotivesRoot.composablePair_targetObject_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetObject =
      pair.right.targetObject :=
  TraceAnalyticMotive.composablePair_targetObject_eq_right
    pair

/-- Public wrapper: the pair source presheaf is the left source presheaf. -/
theorem AnalyticMotivesRoot.composablePair_sourcePresheaf_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourcePresheaf =
      pair.left.sourcePresheaf :=
  TraceAnalyticMotive.composablePair_sourcePresheaf_eq_left
    pair

/-- Public wrapper: the pair middle presheaf is the left target presheaf. -/
theorem AnalyticMotivesRoot.composablePair_middlePresheaf_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middlePresheaf =
      pair.left.targetPresheaf :=
  TraceAnalyticMotive.composablePair_middlePresheaf_eq_left
    pair

/-- Public wrapper: the pair target presheaf is the right target presheaf. -/
theorem AnalyticMotivesRoot.composablePair_targetPresheaf_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetPresheaf =
      pair.right.targetPresheaf :=
  TraceAnalyticMotive.composablePair_targetPresheaf_eq_right
    pair

/-- Public wrapper: the pair source generator is the left source generator. -/
theorem AnalyticMotivesRoot.composablePair_sourceGenerator_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator =
      pair.left.sourceGenerator :=
  TraceAnalyticMotive.composablePair_sourceGenerator_eq_left
    pair

/-- Public wrapper: the pair middle generator is the left target generator. -/
theorem AnalyticMotivesRoot.composablePair_middleGenerator_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator =
      pair.left.targetGenerator :=
  TraceAnalyticMotive.composablePair_middleGenerator_eq_left
    pair

/-- Public wrapper: the pair target generator is the right target generator. -/
theorem AnalyticMotivesRoot.composablePair_targetGenerator_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetGenerator =
      pair.right.targetGenerator :=
  TraceAnalyticMotive.composablePair_targetGenerator_eq_right
    pair

/-- Public wrapper: the pair source localized object is the left source localized object. -/
theorem AnalyticMotivesRoot.composablePair_sourceLocalizedObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceLocalizedObject =
      pair.left.sourceGenerator.localizedObject :=
  TraceAnalyticMotive.composablePair_sourceLocalizedObject_eq_left
    pair

/-- Public wrapper: the pair middle localized object is the left target localized object. -/
theorem AnalyticMotivesRoot.composablePair_middleLocalizedObject_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleLocalizedObject =
      pair.left.targetGenerator.localizedObject :=
  TraceAnalyticMotive.composablePair_middleLocalizedObject_eq_left
    pair

/-- Public wrapper: the pair target localized object is the right target localized object. -/
theorem AnalyticMotivesRoot.composablePair_targetLocalizedObject_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetLocalizedObject =
      pair.right.targetGenerator.localizedObject :=
  TraceAnalyticMotive.composablePair_targetLocalizedObject_eq_right
    pair

/-- Public wrapper: the middle trace object equality carried by a composable pair. -/
theorem AnalyticMotivesRoot.composablePair_middleObject_eq
    (pair : TraceLocalizationInputComposablePair) :
    pair.left.targetObject =
      pair.right.sourceObject :=
  TraceAnalyticMotive.composablePair_middleObject_eq
    pair

/-- Public wrapper: the pair middle object agrees with the right input source. -/
theorem AnalyticMotivesRoot.composablePair_middleObject_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleObject =
      pair.right.sourceObject :=
  TraceAnalyticMotive.composablePair_middleObject_eq_right_source
    pair

/-- Public wrapper: the pair middle presheaf agrees with the right source presheaf. -/
theorem AnalyticMotivesRoot.composablePair_middlePresheaf_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middlePresheaf =
      pair.right.sourcePresheaf :=
  TraceAnalyticMotive.composablePair_middlePresheaf_eq_right_source
    pair

/-- Public wrapper: the source generator remembers the pair source object. -/
theorem AnalyticMotivesRoot.composablePair_sourceGenerator_traceObject
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator.traceObject =
      pair.sourceObject :=
  TraceAnalyticMotive.composablePair_sourceGenerator_traceObject
    pair

/-- Public wrapper: the middle generator remembers the pair middle object. -/
theorem AnalyticMotivesRoot.composablePair_middleGenerator_traceObject
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator.traceObject =
      pair.middleObject :=
  TraceAnalyticMotive.composablePair_middleGenerator_traceObject
    pair

/-- Public wrapper: the target generator remembers the pair target object. -/
theorem AnalyticMotivesRoot.composablePair_targetGenerator_traceObject
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetGenerator.traceObject =
      pair.targetObject :=
  TraceAnalyticMotive.composablePair_targetGenerator_traceObject
    pair

/-- Public wrapper: the source generator has the pair source presheaf. -/
theorem AnalyticMotivesRoot.composablePair_sourceGenerator_presheaf
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator.presheaf =
      pair.sourcePresheaf :=
  TraceAnalyticMotive.composablePair_sourceGenerator_presheaf
    pair

/-- Public wrapper: the middle generator has the pair middle presheaf. -/
theorem AnalyticMotivesRoot.composablePair_middleGenerator_presheaf
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator.presheaf =
      pair.middlePresheaf :=
  TraceAnalyticMotive.composablePair_middleGenerator_presheaf
    pair

/-- Public wrapper: the target generator has the pair target presheaf. -/
theorem AnalyticMotivesRoot.composablePair_targetGenerator_presheaf
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetGenerator.presheaf =
      pair.targetPresheaf :=
  TraceAnalyticMotive.composablePair_targetGenerator_presheaf
    pair

/-- Public wrapper: the middle compact-generator endpoints agree. -/
theorem AnalyticMotivesRoot.composablePair_middleGenerator_eq
    (pair : TraceLocalizationInputComposablePair) :
    pair.left.targetGenerator =
      pair.right.sourceGenerator :=
  TraceAnalyticMotive.composablePair_middleGenerator_eq
    pair

/-- Public wrapper: the reversed middle compact-generator endpoint equality. -/
theorem AnalyticMotivesRoot.composablePair_middleGenerator_eq_symm
    (pair : TraceLocalizationInputComposablePair) :
    pair.right.sourceGenerator =
      pair.left.targetGenerator :=
  TraceAnalyticMotive.composablePair_middleGenerator_eq_symm
    pair

/-- Public wrapper: the pair middle generator agrees with the right input source. -/
theorem AnalyticMotivesRoot.composablePair_middleGenerator_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator =
      pair.right.sourceGenerator :=
  TraceAnalyticMotive.composablePair_middleGenerator_eq_right_source
    pair

/-- Public wrapper: the right input source agrees with the pair middle generator. -/
theorem AnalyticMotivesRoot.composablePair_right_source_eq_middleGenerator
    (pair : TraceLocalizationInputComposablePair) :
    pair.right.sourceGenerator =
      pair.middleGenerator :=
  TraceAnalyticMotive.composablePair_right_source_eq_middleGenerator
    pair

/-- Public wrapper: the source localized object has the pair source object underneath. -/
theorem AnalyticMotivesRoot.composablePair_sourceLocalizedObject_underlying
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceLocalizedObject.underlying =
      pair.sourceObject :=
  TraceAnalyticMotive.composablePair_sourceLocalizedObject_underlying
    pair

/-- Public wrapper: the middle localized object has the pair middle object underneath. -/
theorem AnalyticMotivesRoot.composablePair_middleLocalizedObject_underlying
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleLocalizedObject.underlying =
      pair.middleObject :=
  TraceAnalyticMotive.composablePair_middleLocalizedObject_underlying
    pair

/-- Public wrapper: the target localized object has the pair target object underneath. -/
theorem AnalyticMotivesRoot.composablePair_targetLocalizedObject_underlying
    (pair : TraceLocalizationInputComposablePair) :
    pair.targetLocalizedObject.underlying =
      pair.targetObject :=
  TraceAnalyticMotive.composablePair_targetLocalizedObject_underlying
    pair

/-- Public wrapper: the middle localized object agrees with the right source. -/
theorem AnalyticMotivesRoot.composablePair_middleLocalizedObject_eq_right_source
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleLocalizedObject =
      pair.right.sourceGenerator.localizedObject :=
  TraceAnalyticMotive.composablePair_middleLocalizedObject_eq_right_source
    pair

/-- Public wrapper: the right source localized object agrees with the pair middle. -/
theorem AnalyticMotivesRoot.composablePair_right_sourceLocalizedObject_eq_middle
    (pair : TraceLocalizationInputComposablePair) :
    pair.right.sourceGenerator.localizedObject =
      pair.middleLocalizedObject :=
  TraceAnalyticMotive.composablePair_right_sourceLocalizedObject_eq_middle
    pair

end AnalyticMotives
end LFunctions
end Boundary
