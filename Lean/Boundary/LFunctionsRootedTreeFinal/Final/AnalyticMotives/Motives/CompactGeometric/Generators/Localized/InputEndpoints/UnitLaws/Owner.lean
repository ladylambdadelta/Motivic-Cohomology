import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Identities.Owner

/-!
# Unit laws for localization-input endpoint morphisms

This file records the source and target identity laws for the compact-generator
morphism attached to a concrete localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source identity followed by the input generator hom is the input generator hom. -/
theorem TraceLocalizationInput.id_comp_generatorHom
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.generatorHom =
      input.generatorHom :=
  TraceCorQHom.left_id
    input.generatorHom

/-- The input generator hom followed by the target identity is the input generator hom. -/
theorem TraceLocalizationInput.generatorHom_comp_id
    (input : TraceLocalizationInput) :
    input.generatorHom ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator) =
      input.generatorHom :=
  TraceCorQHom.right_id
    input.generatorHom

/-- The trace hom of the left unit law is the trace hom of the input. -/
theorem TraceLocalizationInput.id_comp_generatorHom_traceHom
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.generatorHom).traceHom =
      input.traceHom :=
  Eq.trans
    (congrArg
      (fun morphism =>
        morphism.traceHom)
      (TraceLocalizationInput.id_comp_generatorHom input))
    (TraceLocalizationInput.generatorHom_traceHom input)

/-- The trace hom of the right unit law is the trace hom of the input. -/
theorem TraceLocalizationInput.generatorHom_comp_id_traceHom
    (input : TraceLocalizationInput) :
    (input.generatorHom ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).traceHom =
      input.traceHom :=
  Eq.trans
    (congrArg
      (fun morphism =>
        morphism.traceHom)
      (TraceLocalizationInput.generatorHom_comp_id input))
    (TraceLocalizationInput.generatorHom_traceHom input)

/-- The representable map of the left unit law is the input map. -/
theorem TraceLocalizationInput.id_comp_generatorHom_representableMap
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.generatorHom).representableMap =
      input.map :=
  Eq.trans
    (congrArg
      (fun morphism =>
        morphism.representableMap)
      (TraceLocalizationInput.id_comp_generatorHom input))
    (TraceLocalizationInput.generatorHom_representableMap input)

/-- The representable map of the right unit law is the input map. -/
theorem TraceLocalizationInput.generatorHom_comp_id_representableMap
    (input : TraceLocalizationInput) :
    (input.generatorHom ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).representableMap =
      input.map :=
  Eq.trans
    (congrArg
      (fun morphism =>
        morphism.representableMap)
      (TraceLocalizationInput.generatorHom_comp_id input))
    (TraceLocalizationInput.generatorHom_representableMap input)

end AnalyticMotives
end LFunctions
end Boundary
