import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.CompactInterpretation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Composition.Owner

/-!
# Composition of forward compact interpretations

This file specializes compact composition formulas to the compact
interpretation of forward unstable localization-input arrows.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Right-composition after the forward compact interpretation has the expected trace hom. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_comp_traceHom
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.unstableForwardCompactInterpretation ≫ tail).traceHom =
      input.traceHom ≫ tail.traceHom :=
  TraceLocalizationInput.generatorHom_comp_traceHom
    input
    tail

/-- Left-composition before the forward compact interpretation has the expected trace hom. -/
theorem TraceLocalizationInput.comp_unstableForwardCompactInterpretation_traceHom
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.unstableForwardCompactInterpretation).traceHom =
      lead.traceHom ≫ input.traceHom :=
  TraceLocalizationInput.comp_generatorHom_traceHom
    input
    lead

/-- Right-composition after the forward compact interpretation has the expected presheaf map. -/
theorem TraceLocalizationInput.unstableForwardCompactInterpretation_comp_representableMap
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.unstableForwardCompactInterpretation ≫ tail).representableMap =
      input.map ≫ tail.representableMap :=
  TraceLocalizationInput.generatorHom_comp_representableMap
    input
    tail

/-- Left-composition before the forward compact interpretation has the expected presheaf map. -/
theorem TraceLocalizationInput.comp_unstableForwardCompactInterpretation_representableMap
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.unstableForwardCompactInterpretation).representableMap =
      lead.representableMap ≫ input.map :=
  TraceLocalizationInput.comp_generatorHom_representableMap
    input
    lead

end AnalyticMotives
end LFunctions
end Boundary
