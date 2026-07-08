import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CompactInterpretation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.CompactInterpretation.Associativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.CompactInterpretation.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.CompactInterpretation.Triples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.CompactInterpretation.Units.Owner

/-!
# Public compact interpretation of unstable input arrows

This file exposes the compact `Q`-linear interpretation of forward unstable
localization-input arrows through the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: the forward compact interpretation is the input generator hom. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_eq_generatorHom
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation =
      input.generatorHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_eq_generatorHom
    input

/-- Public wrapper: the forward compact interpretation has the input trace hom. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.traceHom =
      input.traceHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_traceHom
    input

/-- Public wrapper: the forward compact interpretation induces the input map. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.representableMap =
      input.map :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_representableMap
    input

/-- Public wrapper: the compact presheaf functor sends the forward interpretation to the input map. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_presheafFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map
        input.unstableForwardCompactInterpretation =
      input.map :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_presheafFunctor_map
    input

/-- Public wrapper: the lifted map is the Yoneda map of the input trace hom. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_representableObjectMap_eq_yoneda
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map input.traceHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_representableObjectMap_eq_yoneda
    input

/-- Public wrapper: including the lifted map recovers the input map. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_representableObjectMap_inclusion
    (input : TraceLocalizationInput) :
    TraceCorQRepresentablePresheaf.inclusion.map
        input.unstableForwardCompactInterpretation.representableObjectMap =
      input.map :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_representableObjectMap_inclusion
    input

/-- Public wrapper: the compact Yoneda preimage of the lifted map is the interpretation. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_yonedaPreimage
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        input.unstableForwardCompactInterpretation.representableObjectMap =
      input.unstableForwardCompactInterpretation :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_yonedaPreimage
    input

/-- Public wrapper: scalar multiplication of the forward interpretation is trace scalar multiplication. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_smul_traceHom
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    (coefficient • input.unstableForwardCompactInterpretation).traceHom =
      coefficient • input.traceHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_smul_traceHom
    input
    coefficient

end AnalyticMotives
end LFunctions
end Boundary
