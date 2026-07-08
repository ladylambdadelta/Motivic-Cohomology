import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Composition.Owner

/-!
# Public composition around localized input endpoint morphisms

This file exposes trace-hom and presheaf-map composition formulas around
localization input compact-generator morphisms through the public root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: composing an input generator hom on the right has the expected trace hom. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_comp_traceHom
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.generatorHom ≫ tail).traceHom =
      input.traceHom ≫ tail.traceHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_comp_traceHom
    input
    tail

/-- Public wrapper: composing an input generator hom on the left has the expected trace hom. -/
theorem AnalyticMotivesRoot.localizationInput_comp_generatorHom_traceHom
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.generatorHom).traceHom =
      lead.traceHom ≫ input.traceHom :=
  TraceAnalyticMotive.localizationInput_comp_generatorHom_traceHom
    input
    lead

/-- Public wrapper: composing an input generator hom on the right has the expected presheaf map. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_comp_representableMap
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.generatorHom ≫ tail).representableMap =
      input.map ≫ tail.representableMap :=
  TraceAnalyticMotive.localizationInput_generatorHom_comp_representableMap
    input
    tail

/-- Public wrapper: composing an input generator hom on the left has the expected presheaf map. -/
theorem AnalyticMotivesRoot.localizationInput_comp_generatorHom_representableMap
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.generatorHom).representableMap =
      lead.representableMap ≫ input.map :=
  TraceAnalyticMotive.localizationInput_comp_generatorHom_representableMap
    input
    lead

end AnalyticMotives
end LFunctions
end Boundary
