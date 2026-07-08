import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.UnitLaws.Owner

/-!
# Public unit laws for localization-input endpoint morphisms

This file exposes source and target unit laws for input generator morphisms
through the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: source identity followed by the input generator hom is the input. -/
theorem AnalyticMotivesRoot.localizationInput_id_comp_generatorHom
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.generatorHom =
      input.generatorHom :=
  TraceAnalyticMotive.localizationInput_id_comp_generatorHom
    input

/-- Public wrapper: the input generator hom followed by target identity is the input. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_comp_id
    (input : TraceLocalizationInput) :
    input.generatorHom ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator) =
      input.generatorHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_comp_id
    input

/-- Public wrapper: the trace hom of the left unit law is the input trace hom. -/
theorem AnalyticMotivesRoot.localizationInput_id_comp_generatorHom_traceHom
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.generatorHom).traceHom =
      input.traceHom :=
  TraceAnalyticMotive.localizationInput_id_comp_generatorHom_traceHom
    input

/-- Public wrapper: the trace hom of the right unit law is the input trace hom. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_comp_id_traceHom
    (input : TraceLocalizationInput) :
    (input.generatorHom ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).traceHom =
      input.traceHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_comp_id_traceHom
    input

/-- Public wrapper: the representable map of the left unit law is the input map. -/
theorem AnalyticMotivesRoot.localizationInput_id_comp_generatorHom_representableMap
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.generatorHom).representableMap =
      input.map :=
  TraceAnalyticMotive.localizationInput_id_comp_generatorHom_representableMap
    input

/-- Public wrapper: the representable map of the right unit law is the input map. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_comp_id_representableMap
    (input : TraceLocalizationInput) :
    (input.generatorHom ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).representableMap =
      input.map :=
  TraceAnalyticMotive.localizationInput_generatorHom_comp_id_representableMap
    input

end AnalyticMotives
end LFunctions
end Boundary
