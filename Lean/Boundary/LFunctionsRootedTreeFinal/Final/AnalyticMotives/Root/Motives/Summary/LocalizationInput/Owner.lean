import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.CompactCategory.Owner

/-!
# Top-root localization-input summaries

This file exposes localization-input compact-generator hom maps and their
linear behavior under the public analytic-motives root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public motive summary: a localization input is a compact-generator trace hom. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_traceHom
    (input : TraceLocalizationInput) :
    input.generatorHom.traceHom =
      input.traceHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_traceHom
    input

/-- Public motive summary: a localization input generator hom induces the input map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_representableMap
    (input : TraceLocalizationInput) :
    input.generatorHom.representableMap =
      input.map :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_representableMap
    input

/-- Public motive summary: the compact presheaf functor sends an input hom to the input map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_presheafFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map input.generatorHom =
      input.map :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_presheafFunctor_map
    input

/-- Public motive summary: the lifted-Yoneda functor sends an input hom to its lifted map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_representableObjectFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map input.generatorHom =
      input.generatorHom.representableObjectMap :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_representableObjectFunctor_map
    input

/-- Public motive summary: the lifted input map is the Yoneda map of the input trace hom. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_representableObjectMap_eq_yoneda
    (input : TraceLocalizationInput) :
    input.generatorHom.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map input.traceHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_representableObjectMap_eq_yoneda
    input

/-- Public motive summary: including the lifted input map recovers the input map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_representableObjectMap_inclusion
    (input : TraceLocalizationInput) :
    TraceCorQRepresentablePresheaf.inclusion.map
        input.generatorHom.representableObjectMap =
      input.map :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_representableObjectMap_inclusion
    input

/-- Public motive summary: right-composition after an input hom has the expected trace hom. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_comp_traceHom
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.generatorHom ≫ tail).traceHom =
      input.traceHom ≫ tail.traceHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_comp_traceHom
    input
    tail

/-- Public motive summary: left-composition before an input hom has the expected trace hom. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_comp_generatorHom_traceHom
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.generatorHom).traceHom =
      lead.traceHom ≫ input.traceHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_comp_generatorHom_traceHom
    input
    lead

/-- Public motive summary: right-composition after an input hom has the expected presheaf map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_comp_representableMap
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.generatorHom ≫ tail).representableMap =
      input.map ≫ tail.representableMap :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_comp_representableMap
    input
    tail

/-- Public motive summary: left-composition before an input hom has the expected presheaf map. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_comp_generatorHom_representableMap
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.generatorHom).representableMap =
      lead.representableMap ≫ input.map :=
  TraceAnalyticMotive.rootSummary_localizationInput_comp_generatorHom_representableMap
    input
    lead

/-- Public motive summary: zero over an input generator hom is zero on trace homs. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_zero_traceHom
    (input : TraceLocalizationInput) :
    (0 : input.sourceGenerator ⟶ input.targetGenerator).traceHom =
      (0 : input.sourceObject ⟶ input.targetObject) :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_zero_traceHom
    input

/-- Public motive summary: scalar multiplication of an input generator hom is trace scalar multiplication. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_smul_traceHom
    (input : TraceLocalizationInput)
    (coefficient : Rat) :
    (coefficient • input.generatorHom).traceHom =
      coefficient • input.traceHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_smul_traceHom
    input
    coefficient

/-- Public motive summary: negation of an input generator hom is trace-hom negation. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_traceNeg_traceHom
    (input : TraceLocalizationInput) :
    (TraceCorQHom.neg input.generatorHom).traceHom =
      TraceCorQHom.neg input.traceHom :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_traceNeg_traceHom
    input

/-- Public motive summary: self-subtraction of an input generator hom gives zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_generatorHom_traceSub_self
    (input : TraceLocalizationInput) :
    TraceCorQHom.sub input.generatorHom input.generatorHom =
      TraceCorQHom.zero input.sourceObject input.targetObject :=
  TraceAnalyticMotive.rootSummary_localizationInput_generatorHom_traceSub_self
    input

end AnalyticMotives
end LFunctions
end Boundary
