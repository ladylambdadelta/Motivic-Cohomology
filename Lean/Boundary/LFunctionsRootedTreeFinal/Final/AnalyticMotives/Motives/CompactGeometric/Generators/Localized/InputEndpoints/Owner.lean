import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Owner

/-!
# Localized compact-generator endpoints of localization inputs

This file identifies the compact geometric generators attached to the source
and target objects of a concrete localization input, and records their
localized-word objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact geometric source generator attached to a localization input. -/
def TraceLocalizationInput.sourceGenerator
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject input.sourceObject

/-- The compact geometric target generator attached to a localization input. -/
def TraceLocalizationInput.targetGenerator
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator :=
  TraceAnalyticGeometricGenerator.ofTraceObject input.targetObject

/-- The source generator remembers the source object of the localization input. -/
theorem TraceLocalizationInput.sourceGenerator_traceObject
    (input : TraceLocalizationInput) :
    input.sourceGenerator.traceObject =
      input.sourceObject :=
  rfl

/-- The target generator remembers the target object of the localization input. -/
theorem TraceLocalizationInput.targetGenerator_traceObject
    (input : TraceLocalizationInput) :
    input.targetGenerator.traceObject =
      input.targetObject :=
  rfl

/-- The source generator localized object is the wrapped localization-input source object. -/
theorem TraceLocalizationInput.sourceGenerator_localizedWordObject
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject input.sourceObject :=
  rfl

/-- The target generator localized object is the wrapped localization-input target object. -/
theorem TraceLocalizationInput.targetGenerator_localizedWordObject
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject input.targetObject :=
  rfl

/-- The source generator localized object has the input source object underneath. -/
theorem TraceLocalizationInput.sourceGenerator_localizedWordObject_underlying
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedWordObject.underlying =
      input.sourceObject :=
  rfl

/-- The target generator localized object has the input target object underneath. -/
theorem TraceLocalizationInput.targetGenerator_localizedWordObject_underlying
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedWordObject.underlying =
      input.targetObject :=
  rfl

/-- The source generator presheaf is the representable source presheaf of the input. -/
theorem TraceLocalizationInput.sourceGenerator_presheaf
    (input : TraceLocalizationInput) :
    input.sourceGenerator.presheaf =
      input.sourcePresheaf :=
  rfl

/-- The target generator presheaf is the representable target presheaf of the input. -/
theorem TraceLocalizationInput.targetGenerator_presheaf
    (input : TraceLocalizationInput) :
    input.targetGenerator.presheaf =
      input.targetPresheaf :=
  rfl

/-- The localization-input trace hom is a compact-generator morphism between its endpoints. -/
def TraceLocalizationInput.generatorHom
    (input : TraceLocalizationInput) :
    input.sourceGenerator ⟶ input.targetGenerator :=
  input.traceHom

/-- The compact-generator morphism attached to an input is its trace hom. -/
theorem TraceLocalizationInput.generatorHom_traceHom
    (input : TraceLocalizationInput) :
    input.generatorHom.traceHom =
      input.traceHom :=
  rfl

/-- The representable map of the compact-generator morphism is the input map. -/
theorem TraceLocalizationInput.generatorHom_representableMap
    (input : TraceLocalizationInput) :
    input.generatorHom.representableMap =
      input.map :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.Hom.representableMap_eq
      input.generatorHom)
    (Eq.symm
      (TraceLocalizationInput.map_eq_representableMap input))

end AnalyticMotives
end LFunctions
end Boundary
