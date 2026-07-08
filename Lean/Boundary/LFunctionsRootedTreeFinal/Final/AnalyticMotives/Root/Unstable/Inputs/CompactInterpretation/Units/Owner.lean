import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CompactInterpretation.Units.Owner

/-!
# Public unit laws for forward compact interpretations

This file exposes unit laws for the compact interpretation of forward unstable
localization-input arrows through the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: right identity for the forward compact interpretation. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_comp_id
    (input : TraceLocalizationInput) :
    input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator) =
      input.unstableForwardCompactInterpretation :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_id
    input

/-- Public wrapper: left identity for the forward compact interpretation. -/
theorem AnalyticMotivesRoot.id_comp_unstableForwardCompactInterpretation
    (input : TraceLocalizationInput) :
    (𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation =
      input.unstableForwardCompactInterpretation :=
  TraceAnalyticMotive.id_comp_unstableForwardCompactInterpretation
    input

/-- Public wrapper: right identity for the trace hom of the forward interpretation. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_comp_id_traceHom
    (input : TraceLocalizationInput) :
    (input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).traceHom =
      input.traceHom :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_id_traceHom
    input

/-- Public wrapper: left identity for the trace hom of the forward interpretation. -/
theorem AnalyticMotivesRoot.id_comp_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation).traceHom =
      input.traceHom :=
  TraceAnalyticMotive.id_comp_unstableForwardCompactInterpretation_traceHom
    input

/-- Public wrapper: right identity for the presheaf map of the forward interpretation. -/
theorem AnalyticMotivesRoot.unstableForwardCompactInterpretation_comp_id_representableMap
    (input : TraceLocalizationInput) :
    (input.unstableForwardCompactInterpretation ≫
        (𝟙 input.targetGenerator : input.targetGenerator ⟶ input.targetGenerator)).representableMap =
      input.map :=
  TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_id_representableMap
    input

/-- Public wrapper: left identity for the presheaf map of the forward interpretation. -/
theorem AnalyticMotivesRoot.id_comp_unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput) :
    ((𝟙 input.sourceGenerator : input.sourceGenerator ⟶ input.sourceGenerator) ≫
        input.unstableForwardCompactInterpretation).representableMap =
      input.map :=
  TraceAnalyticMotive.id_comp_unstableForwardCompactInterpretation_representableMap
    input

end AnalyticMotives
end LFunctions
end Boundary
