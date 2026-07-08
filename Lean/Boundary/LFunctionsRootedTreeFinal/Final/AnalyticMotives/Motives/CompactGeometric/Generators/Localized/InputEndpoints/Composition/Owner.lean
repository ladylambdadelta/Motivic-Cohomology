import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Functoriality.Owner

/-!
# Composition around localized input endpoint morphisms

This file specializes compact-generator composition formulas to composites
whose left or right factor is the compact-generator morphism attached to a
localization input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composing an input generator hom on the right has the expected trace hom. -/
theorem TraceLocalizationInput.generatorHom_comp_traceHom
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.generatorHom ≫ tail).traceHom =
      input.traceHom ≫ tail.traceHom :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.comp_traceHom
      input.generatorHom
      tail)
    (congrArg
      (fun traceHom =>
        traceHom ≫ tail.traceHom)
      (TraceLocalizationInput.generatorHom_traceHom input))

/-- Composing an input generator hom on the left has the expected trace hom. -/
theorem TraceLocalizationInput.comp_generatorHom_traceHom
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.generatorHom).traceHom =
      lead.traceHom ≫ input.traceHom :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.comp_traceHom
      lead
      input.generatorHom)
    (congrArg
      (fun traceHom =>
        lead.traceHom ≫ traceHom)
      (TraceLocalizationInput.generatorHom_traceHom input))

/-- Composing an input generator hom on the right has the expected presheaf map. -/
theorem TraceLocalizationInput.generatorHom_comp_representableMap
    (input : TraceLocalizationInput)
    {target : TraceAnalyticGeometricGenerator}
    (tail : input.targetGenerator ⟶ target) :
    (input.generatorHom ≫ tail).representableMap =
      input.map ≫ tail.representableMap :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.comp_representableMap
      input.generatorHom
      tail)
    (congrArg
      (fun map =>
        map ≫ tail.representableMap)
      (TraceLocalizationInput.generatorHom_representableMap input))

/-- Composing an input generator hom on the left has the expected presheaf map. -/
theorem TraceLocalizationInput.comp_generatorHom_representableMap
    (input : TraceLocalizationInput)
    {source : TraceAnalyticGeometricGenerator}
    (lead : source ⟶ input.sourceGenerator) :
    (lead ≫ input.generatorHom).representableMap =
      lead.representableMap ≫ input.map :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.comp_representableMap
      lead
      input.generatorHom)
    (congrArg
      (fun map =>
        lead.representableMap ≫ map)
      (TraceLocalizationInput.generatorHom_representableMap input))

end AnalyticMotives
end LFunctions
end Boundary
