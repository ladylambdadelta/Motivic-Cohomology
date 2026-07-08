import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Functoriality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Linear.Owner

/-!
# Compact interpretation of unstable input arrows

This file records the compact `Q`-linear interpretation of the forward
unstable localization-input arrow.  Formal inverse arrows are intentionally
not given a compact interpretation here; they live in the localized-word
category until an actual compact inverse has been constructed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact interpretation of the forward unstable arrow of a localization input. -/
def TraceLocalizationInput.unstableForwardCompactInterpretation
    (input : TraceLocalizationInput) :
    input.sourceGenerator ⟶ input.targetGenerator :=
  input.generatorHom

/-- The forward compact interpretation is the input generator hom. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation =
      input.generatorHom :=
  rfl

/-- The forward compact interpretation has the input trace hom underneath. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.traceHom =
      input.traceHom :=
  TraceLocalizationInput.generatorHom_traceHom
    input

/-- The forward compact interpretation induces the input presheaf map. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.representableMap =
      input.map :=
  TraceLocalizationInput.generatorHom_representableMap
    input

/-- The compact presheaf functor sends the forward interpretation to the input map. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_presheafFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map
        input.unstableForwardCompactInterpretation =
      input.map :=
  TraceLocalizationInput.generatorHom_presheafFunctor_map
    input

/-- The lifted map of the forward compact interpretation is the Yoneda map of the input trace hom. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_representableObjectMap_eq_yoneda
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map input.traceHom :=
  TraceLocalizationInput.generatorHom_representableObjectMap_eq_yoneda
    input

/-- Including the lifted map of the forward compact interpretation recovers the input map. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_representableObjectMap_inclusion
    (input : TraceLocalizationInput) :
    TraceCorQRepresentablePresheaf.inclusion.map
        input.unstableForwardCompactInterpretation.representableObjectMap =
      input.map :=
  TraceLocalizationInput.generatorHom_representableObjectMap_inclusion
    input

/-- The compact Yoneda preimage of the lifted forward interpretation is the interpretation. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_yonedaPreimage
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        input.unstableForwardCompactInterpretation.representableObjectMap =
      input.unstableForwardCompactInterpretation :=
  TraceLocalizationInput.generatorHom_yonedaPreimage_representableObjectMap
    input

/-- Scalar multiplication of the forward compact interpretation is trace scalar multiplication. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_smul_traceHom
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    (coefficient • input.unstableForwardCompactInterpretation).traceHom =
      coefficient • input.traceHom :=
  TraceLocalizationInput.generatorHom_smul_traceHom
    input
    coefficient

end AnalyticMotives
end LFunctions
end Boundary
