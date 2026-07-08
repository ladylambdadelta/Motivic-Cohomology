import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.EndpointTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Identities.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.UnitLaws.Owner

/-!
# Motive-root localization-input endpoint wrappers

This file mirrors the compact-generator endpoint facts for concrete
localization inputs under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root localization-input source generator remembers the source object. -/
theorem TraceAnalyticMotive.localizationInput_sourceGenerator_traceObject
    (input : TraceLocalizationInput) :
    input.sourceGenerator.traceObject =
      input.sourceObject :=
  TraceLocalizationInput.sourceGenerator_traceObject
    input

/-- Motive-root localization-input target generator remembers the target object. -/
theorem TraceAnalyticMotive.localizationInput_targetGenerator_traceObject
    (input : TraceLocalizationInput) :
    input.targetGenerator.traceObject =
      input.targetObject :=
  TraceLocalizationInput.targetGenerator_traceObject
    input

/-- Motive-root source endpoint localized object is the wrapped input source object. -/
theorem TraceAnalyticMotive.localizationInput_sourceGenerator_localizedWordObject
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject input.sourceObject :=
  TraceLocalizationInput.sourceGenerator_localizedWordObject
    input

/-- Motive-root target endpoint localized object is the wrapped input target object. -/
theorem TraceAnalyticMotive.localizationInput_targetGenerator_localizedWordObject
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedWordObject =
      TraceLocalizedWordObject.ofTraceObject input.targetObject :=
  TraceLocalizationInput.targetGenerator_localizedWordObject
    input

/-- Motive-root source endpoint localized object has the input source object underneath. -/
theorem TraceAnalyticMotive.localizationInput_sourceGenerator_localizedWordObject_underlying
    (input : TraceLocalizationInput) :
    input.sourceGenerator.localizedWordObject.underlying =
      input.sourceObject :=
  TraceLocalizationInput.sourceGenerator_localizedWordObject_underlying
    input

/-- Motive-root target endpoint localized object has the input target object underneath. -/
theorem TraceAnalyticMotive.localizationInput_targetGenerator_localizedWordObject_underlying
    (input : TraceLocalizationInput) :
    input.targetGenerator.localizedWordObject.underlying =
      input.targetObject :=
  TraceLocalizationInput.targetGenerator_localizedWordObject_underlying
    input

/-- Motive-root source endpoint presheaf is the input source presheaf. -/
theorem TraceAnalyticMotive.localizationInput_sourceGenerator_presheaf
    (input : TraceLocalizationInput) :
    input.sourceGenerator.presheaf =
      input.sourcePresheaf :=
  TraceLocalizationInput.sourceGenerator_presheaf
    input

/-- Motive-root target endpoint presheaf is the input target presheaf. -/
theorem TraceAnalyticMotive.localizationInput_targetGenerator_presheaf
    (input : TraceLocalizationInput) :
    input.targetGenerator.presheaf =
      input.targetPresheaf :=
  TraceLocalizationInput.targetGenerator_presheaf
    input

/-- Motive-root localization-input generator morphism is the input trace hom. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_traceHom
    (input : TraceLocalizationInput) :
    input.generatorHom.traceHom =
      input.traceHom :=
  TraceLocalizationInput.generatorHom_traceHom
    input

/-- Motive-root localization-input generator morphism induces the input map. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_representableMap
    (input : TraceLocalizationInput) :
    input.generatorHom.representableMap =
      input.map :=
  TraceLocalizationInput.generatorHom_representableMap
    input

end AnalyticMotives
end LFunctions
end Boundary
