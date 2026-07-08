import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.UnitLaws.Owner

/-!
# Motive-root unit laws for localization-input endpoint morphisms

This file exposes source and target unit laws for input generator morphisms
through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: source identity followed by the input generator hom is the input. -/
theorem TraceAnalyticMotive.localizationInput_id_comp_generatorHom
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.generatorHom =
      input.generatorHom :=
  TraceLocalizationInput.id_comp_generatorHom
    input

/-- Motive-root wrapper: the input generator hom followed by target identity is the input. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_comp_id
    (input : TraceLocalizationInput) :
    input.generatorHom ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator) =
      input.generatorHom :=
  TraceLocalizationInput.generatorHom_comp_id
    input

/-- Motive-root wrapper: the trace hom of the left unit law is the input trace hom. -/
theorem TraceAnalyticMotive.localizationInput_id_comp_generatorHom_traceHom
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.generatorHom).traceHom =
      input.traceHom :=
  TraceLocalizationInput.id_comp_generatorHom_traceHom
    input

/-- Motive-root wrapper: the trace hom of the right unit law is the input trace hom. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_comp_id_traceHom
    (input : TraceLocalizationInput) :
    (input.generatorHom ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).traceHom =
      input.traceHom :=
  TraceLocalizationInput.generatorHom_comp_id_traceHom
    input

/-- Motive-root wrapper: the representable map of the left unit law is the input map. -/
theorem TraceAnalyticMotive.localizationInput_id_comp_generatorHom_representableMap
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.generatorHom).representableMap =
      input.map :=
  TraceLocalizationInput.id_comp_generatorHom_representableMap
    input

/-- Motive-root wrapper: the representable map of the right unit law is the input map. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_comp_id_representableMap
    (input : TraceLocalizationInput) :
    (input.generatorHom ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).representableMap =
      input.map :=
  TraceLocalizationInput.generatorHom_comp_id_representableMap
    input

end AnalyticMotives
end LFunctions
end Boundary
