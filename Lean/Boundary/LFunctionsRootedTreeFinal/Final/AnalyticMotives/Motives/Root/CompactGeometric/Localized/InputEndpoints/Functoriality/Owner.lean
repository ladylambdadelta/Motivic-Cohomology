import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Functoriality.Owner

/-!
# Motive-root functoriality of localized input endpoints

This file exposes the compact presheaf and lifted-Yoneda functoriality of
localization input compact-generator morphisms through the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the compact presheaf functor sends an input hom to the input map. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_presheafFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map input.generatorHom =
      input.map :=
  TraceLocalizationInput.generatorHom_presheafFunctor_map
    input

/-- Motive-root wrapper: the lifted-Yoneda functor sends an input hom to its lifted map. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_representableObjectFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map input.generatorHom =
      input.generatorHom.representableObjectMap :=
  TraceLocalizationInput.generatorHom_representableObjectFunctor_map
    input

/-- Motive-root wrapper: the lifted input map is the Yoneda map of the input trace hom. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_representableObjectMap_eq_yoneda
    (input : TraceLocalizationInput) :
    input.generatorHom.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map input.traceHom :=
  TraceLocalizationInput.generatorHom_representableObjectMap_eq_yoneda
    input

/-- Motive-root wrapper: including the lifted input map recovers the input map. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_representableObjectMap_inclusion
    (input : TraceLocalizationInput) :
    TraceCorQRepresentablePresheaf.inclusion.map
        input.generatorHom.representableObjectMap =
      input.map :=
  TraceLocalizationInput.generatorHom_representableObjectMap_inclusion
    input

/-- Motive-root wrapper: the compact Yoneda preimage of the lifted input map is the input hom. -/
theorem TraceAnalyticMotive.localizationInput_generatorHom_yonedaPreimage_representableObjectMap
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        input.generatorHom.representableObjectMap =
      input.generatorHom :=
  TraceLocalizationInput.generatorHom_yonedaPreimage_representableObjectMap
    input

end AnalyticMotives
end LFunctions
end Boundary
