import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.CompactInterpretation.Owner

/-!
# Unit laws for forward compact interpretations

This file specializes compact-generator left and right unit laws to the compact
interpretation of forward unstable localization-input arrows.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Right identity for the forward compact interpretation. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_comp_id
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator) =
      input.unstableForwardCompactInterpretation :=
  TraceCorQHom.right_id
    input.unstableForwardCompactInterpretation

/-- Left identity for the forward compact interpretation. -/
theorem TraceLocalizationInput.id_comp_unstableForwardCompactInterpretation
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation =
      input.unstableForwardCompactInterpretation :=
  TraceCorQHom.left_id
    input.unstableForwardCompactInterpretation

/-- Right identity for the trace hom of the forward compact interpretation. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_comp_id_traceHom
    (input : TraceLocalizationInput) :
    (input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).traceHom =
      input.traceHom :=
  Eq.trans
    (congrArg
      (fun morphism =>
        morphism.traceHom)
      (TraceLocalizationInput.unstableForwardCompactInterpretation_comp_id
        input))
    (TraceLocalizationInput.unstableForwardCompactInterpretation_traceHom
      input)

/-- Left identity for the trace hom of the forward compact interpretation. -/
theorem TraceLocalizationInput.id_comp_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation).traceHom =
      input.traceHom :=
  Eq.trans
    (congrArg
      (fun morphism =>
        morphism.traceHom)
      (TraceLocalizationInput.id_comp_unstableForwardCompactInterpretation
        input))
    (TraceLocalizationInput.unstableForwardCompactInterpretation_traceHom
      input)

/-- Right identity for the presheaf map of the forward compact interpretation. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_comp_id_representableMap
    (input : TraceLocalizationInput) :
    (input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).representableMap =
      input.map :=
  Eq.trans
    (congrArg
      (fun morphism =>
        morphism.representableMap)
      (TraceLocalizationInput.unstableForwardCompactInterpretation_comp_id
        input))
    (TraceLocalizationInput.unstableForwardCompactInterpretation_representableMap
      input)

/-- Left identity for the presheaf map of the forward compact interpretation. -/
theorem TraceLocalizationInput.id_comp_unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation).representableMap =
      input.map :=
  Eq.trans
    (congrArg
      (fun morphism =>
        morphism.representableMap)
      (TraceLocalizationInput.id_comp_unstableForwardCompactInterpretation
        input))
    (TraceLocalizationInput.unstableForwardCompactInterpretation_representableMap
      input)

end AnalyticMotives
end LFunctions
end Boundary
