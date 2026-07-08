import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.CompactInterpretation.Composition.Owner

/-!
# Motive-root composition of forward compact interpretations

This file exposes composition formulas for the compact interpretation of
forward unstable localization-input arrows through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: right-composition after the forward interpretation has the expected trace hom. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_traceHom
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.unstableForwardCompactInterpretation ≫ tail).traceHom =
      input.traceHom ≫ tail.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_comp_traceHom
    input
    tail

/-- Motive-root wrapper: left-composition before the forward interpretation has the expected trace hom. -/
theorem TraceAnalyticMotive.comp_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.unstableForwardCompactInterpretation).traceHom =
      lead.traceHom ≫ input.traceHom :=
  TraceLocalizationInput.comp_unstableForwardCompactInterpretation_traceHom
    input
    lead

/-- Motive-root wrapper: right-composition after the forward interpretation has the expected presheaf map. -/
theorem TraceAnalyticMotive.unstableForwardCompactInterpretation_comp_representableMap
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.unstableForwardCompactInterpretation ≫ tail).representableMap =
      input.map ≫ tail.representableMap :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_comp_representableMap
    input
    tail

/-- Motive-root wrapper: left-composition before the forward interpretation has the expected presheaf map. -/
theorem TraceAnalyticMotive.comp_unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.unstableForwardCompactInterpretation).representableMap =
      lead.representableMap ≫ input.map :=
  TraceLocalizationInput.comp_unstableForwardCompactInterpretation_representableMap
    input
    lead

end AnalyticMotives
end LFunctions
end Boundary
