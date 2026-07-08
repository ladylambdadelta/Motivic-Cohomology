import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.CompactCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Owner

/-!
# Motive-root localization-input summaries

This file exposes root summary theorems for localization-input compact-generator
hom maps and their linear behavior.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: a localization input is a compact-generator trace hom. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_traceHom
    (input : TraceLocalizationInput) :
    input.generatorHom.traceHom =
      input.traceHom :=
  TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_traceHom
    input

/-- Motive-root summary: a localization input generator hom induces the input map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_representableMap
    (input : TraceLocalizationInput) :
    input.generatorHom.representableMap =
      input.map :=
  TraceAnalyticMotive.compactGenerator_localizationInput_generatorHom_representableMap
    input

/-- Motive-root summary: the compact presheaf functor sends an input hom to the input map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_presheafFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map input.generatorHom =
      input.map :=
  TraceAnalyticMotive.localizationInput_generatorHom_presheafFunctor_map
    input

/-- Motive-root summary: the lifted-Yoneda functor sends an input hom to its lifted map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_representableObjectFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map input.generatorHom =
      input.generatorHom.representableObjectMap :=
  TraceAnalyticMotive.localizationInput_generatorHom_representableObjectFunctor_map
    input

/-- Motive-root summary: the lifted input map is the Yoneda map of the input trace hom. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_representableObjectMap_eq_yoneda
    (input : TraceLocalizationInput) :
    input.generatorHom.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map input.traceHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_representableObjectMap_eq_yoneda
    input

/-- Motive-root summary: including the lifted input map recovers the input map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_representableObjectMap_inclusion
    (input : TraceLocalizationInput) :
    TraceCorQRepresentablePresheaf.inclusion.map
        input.generatorHom.representableObjectMap =
      input.map :=
  TraceAnalyticMotive.localizationInput_generatorHom_representableObjectMap_inclusion
    input

/-- Motive-root summary: right-composition after an input hom has the expected trace hom. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_comp_traceHom
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.generatorHom ≫ tail).traceHom =
      input.traceHom ≫ tail.traceHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_comp_traceHom
    input
    tail

/-- Motive-root summary: left-composition before an input hom has the expected trace hom. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_comp_generatorHom_traceHom
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.generatorHom).traceHom =
      lead.traceHom ≫ input.traceHom :=
  TraceAnalyticMotive.localizationInput_comp_generatorHom_traceHom
    input
    lead

/-- Motive-root summary: right-composition after an input hom has the expected presheaf map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_comp_representableMap
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.generatorHom ≫ tail).representableMap =
      input.map ≫ tail.representableMap :=
  TraceAnalyticMotive.localizationInput_generatorHom_comp_representableMap
    input
    tail

/-- Motive-root summary: left-composition before an input hom has the expected presheaf map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_comp_generatorHom_representableMap
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.generatorHom).representableMap =
      lead.representableMap ≫ input.map :=
  TraceAnalyticMotive.localizationInput_comp_generatorHom_representableMap
    input
    lead

/-- Motive-root summary: zero over an input generator hom is zero on trace homs. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_zero_traceHom
    (input : TraceLocalizationInput) :
    (0 : input.sourceGenerator ⟶ input.targetGenerator).traceHom =
      (0 : input.sourceObject ⟶ input.targetObject) :=
  TraceAnalyticMotive.localizationInput_generatorHom_zero_traceHom
    input

/-- Motive-root summary: scalar multiplication of an input generator hom is trace scalar multiplication. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_smul_traceHom
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    (coefficient • input.generatorHom).traceHom =
      coefficient • input.traceHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_smul_traceHom
    input
    coefficient

/-- Motive-root summary: negation of an input generator hom is trace-hom negation. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_traceNeg_traceHom
    (input : TraceLocalizationInput) :
    (TraceCorQHom.neg input.generatorHom).traceHom =
      TraceCorQHom.neg input.traceHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_traceNeg_traceHom
    input

/-- Motive-root summary: self-subtraction of an input generator hom gives zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_traceSub_self
    (input : TraceLocalizationInput) :
    TraceCorQHom.sub input.generatorHom input.generatorHom =
      TraceCorQHom.zero input.sourceObject input.targetObject :=
  TraceAnalyticMotive.localizationInput_generatorHom_traceSub_self
    input

end AnalyticMotives
end LFunctions
end Boundary
