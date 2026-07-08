import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.CompactInterpretation.Units.Owner

/-!
# Motive-root unit laws for forward compact interpretations

This file exposes unit laws for the compact interpretation of forward unstable
localization-input arrows through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: right identity for the forward compact interpretation. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_id
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator) =
      input.unstableForwardCompactInterpretation :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_comp_id
    input

/-- Motive-root wrapper: left identity for the forward compact interpretation. -/
theorem TraceAnalyticMotive.id_comp_unstableForwardCompactInterpretation
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation =
      input.unstableForwardCompactInterpretation :=
  TraceLocalizationInput.id_comp_unstableForwardCompactInterpretation
    input

/-- Motive-root wrapper: right identity for the trace hom of the forward interpretation. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_id_traceHom
    (input : TraceLocalizationInput) :
    (input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).traceHom =
      input.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_comp_id_traceHom
    input

/-- Motive-root wrapper: left identity for the trace hom of the forward interpretation. -/
theorem TraceAnalyticMotive.id_comp_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation).traceHom =
      input.traceHom :=
  TraceLocalizationInput.id_comp_unstableForwardCompactInterpretation_traceHom
    input

/-- Motive-root wrapper: right identity for the presheaf map of the forward interpretation. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_id_representableMap
    (input : TraceLocalizationInput) :
    (input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).representableMap =
      input.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_comp_id_representableMap
    input

/-- Motive-root wrapper: left identity for the presheaf map of the forward interpretation. -/
theorem TraceAnalyticMotive.id_comp_unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation).representableMap =
      input.map :=
  TraceLocalizationInput.id_comp_unstableForwardCompactInterpretation_representableMap
    input

end AnalyticMotives
end LFunctions
end Boundary
