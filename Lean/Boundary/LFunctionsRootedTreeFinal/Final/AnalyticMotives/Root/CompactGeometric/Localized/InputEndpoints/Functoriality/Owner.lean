import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.Functoriality.Owner

/-!
# Public functoriality of localized input endpoints

This file exposes the compact presheaf and lifted-Yoneda functoriality of
localization input compact-generator morphisms through the public root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: the compact presheaf functor sends an input hom to the input map. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_presheafFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map input.generatorHom =
      input.map :=
  TraceAnalyticMotive.localizationInput_generatorHom_presheafFunctor_map
    input

/-- Public wrapper: the lifted-Yoneda functor sends an input hom to its lifted map. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_representableObjectFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map input.generatorHom =
      input.generatorHom.representableObjectMap :=
  TraceAnalyticMotive.localizationInput_generatorHom_representableObjectFunctor_map
    input

/-- Public wrapper: the lifted input map is the Yoneda map of the input trace hom. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_representableObjectMap_eq_yoneda
    (input : TraceLocalizationInput) :
    input.generatorHom.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map input.traceHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_representableObjectMap_eq_yoneda
    input

/-- Public wrapper: including the lifted input map recovers the input map. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_representableObjectMap_inclusion
    (input : TraceLocalizationInput) :
    TraceCorQRepresentablePresheaf.inclusion.map
        input.generatorHom.representableObjectMap =
      input.map :=
  TraceAnalyticMotive.localizationInput_generatorHom_representableObjectMap_inclusion
    input

/-- Public wrapper: the compact Yoneda preimage of the lifted input map is the input hom. -/
theorem AnalyticMotivesRoot.localizationInput_generatorHom_yonedaPreimage_representableObjectMap
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        input.generatorHom.representableObjectMap =
      input.generatorHom :=
  TraceAnalyticMotive.localizationInput_generatorHom_yonedaPreimage_representableObjectMap
    input

end AnalyticMotives
end LFunctions
end Boundary
