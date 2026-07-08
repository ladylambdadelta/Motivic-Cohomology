import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.CompactInterpretation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CompactInterpretation.Associativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CompactInterpretation.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CompactInterpretation.Triples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CompactInterpretation.Units.Owner

/-!
# Motive-root compact interpretation of unstable input arrows

This file exposes the compact `Q`-linear interpretation of forward unstable
localization-input arrows through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the forward compact interpretation is the input generator hom. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation =
      input.generatorHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_eq_generatorHom
    input

/-- Motive-root wrapper: the forward compact interpretation has the input trace hom. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.traceHom =
      input.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_traceHom
    input

/-- Motive-root wrapper: the forward compact interpretation induces the input map. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.representableMap =
      input.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_representableMap
    input

/-- Motive-root wrapper: the compact presheaf functor sends the forward interpretation to the input map. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_presheafFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map
        input.unstableForwardCompactInterpretation =
      input.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_presheafFunctor_map
    input

/-- Motive-root wrapper: the lifted map is the Yoneda map of the input trace hom. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_representableObjectMap_eq_yoneda
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map input.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_representableObjectMap_eq_yoneda
    input

/-- Motive-root wrapper: including the lifted map recovers the input map. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_representableObjectMap_inclusion
    (input : TraceLocalizationInput) :
    TraceCorQRepresentablePresheaf.inclusion.map
        input.unstableForwardCompactInterpretation.representableObjectMap =
      input.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_representableObjectMap_inclusion
    input

/-- Motive-root wrapper: the compact Yoneda preimage of the lifted map is the interpretation. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_yonedaPreimage
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        input.unstableForwardCompactInterpretation.representableObjectMap =
      input.unstableForwardCompactInterpretation :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_yonedaPreimage
    input

/-- Motive-root wrapper: scalar multiplication of the forward interpretation is trace scalar multiplication. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_smul_traceHom
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    (coefficient • input.unstableForwardCompactInterpretation).traceHom =
      coefficient • input.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_smul_traceHom
    input
    coefficient

end AnalyticMotives
end LFunctions
end Boundary
