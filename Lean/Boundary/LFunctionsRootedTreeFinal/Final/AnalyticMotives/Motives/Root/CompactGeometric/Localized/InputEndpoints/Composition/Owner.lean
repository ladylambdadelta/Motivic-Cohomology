import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Composition.Owner

/-!
# Motive-root composition around localized input endpoint morphisms

This file exposes trace-hom and presheaf-map composition formulas around
localization input compact-generator morphisms through the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: composing an input generator hom on the right has the expected trace hom. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_comp_traceHom
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.generatorHom ≫ tail).traceHom =
      input.traceHom ≫ tail.traceHom :=
  TraceLocalizationInput.generatorHom_comp_traceHom
    input
    tail

/-- Motive-root wrapper: composing an input generator hom on the left has the expected trace hom. -/
theorem TraceAnalyticMotive.localizationInput_comp_generatorHom_traceHom
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.generatorHom).traceHom =
      lead.traceHom ≫ input.traceHom :=
  TraceLocalizationInput.comp_generatorHom_traceHom
    input
    lead

/-- Motive-root wrapper: composing an input generator hom on the right has the expected presheaf map. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_comp_representableMap
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.generatorHom ≫ tail).representableMap =
      input.map ≫ tail.representableMap :=
  TraceLocalizationInput.generatorHom_comp_representableMap
    input
    tail

/-- Motive-root wrapper: composing an input generator hom on the left has the expected presheaf map. -/
theorem TraceAnalyticMotive.localizationInput_comp_generatorHom_representableMap
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.generatorHom).representableMap =
      lead.representableMap ≫ input.map :=
  TraceLocalizationInput.comp_generatorHom_representableMap
    input
    lead

end AnalyticMotives
end LFunctions
end Boundary
