import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Owner

/-!
# Functoriality of localized input endpoints

This file records how the compact-generator morphism attached to a
localization input is seen by the compact presheaf and lifted-Yoneda functors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact presheaf functor sends an input generator hom to the input map. -/
theorem TraceLocalizationInput.generatorHom_presheafFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map input.generatorHom =
      input.map :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.presheafFunctor_map
      input.generatorHom)
    (TraceLocalizationInput.generatorHom_representableMap input)

/-- The compact lifted-Yoneda functor sends an input generator hom to its lifted map. -/
theorem TraceLocalizationInput.generatorHom_representableObjectFunctor_map
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map input.generatorHom =
      input.generatorHom.representableObjectMap :=
  TraceAnalyticGeometricGenerator.representableObjectFunctor_map
    input.generatorHom

/-- The lifted map of an input generator hom is the Yoneda map of the input trace hom. -/
theorem TraceLocalizationInput.generatorHom_representableObjectMap_eq_yoneda
    (input : TraceLocalizationInput) :
    input.generatorHom.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map input.traceHom :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.Hom.representableObjectMap_eq
      input.generatorHom)
    (congrArg
      (fun traceHom =>
        (TraceCorQRepresentablePresheaf.yoneda).map traceHom)
      (TraceLocalizationInput.generatorHom_traceHom input))

/-- Including the lifted input map recovers the concrete input presheaf map. -/
theorem TraceLocalizationInput.generatorHom_representableObjectMap_inclusion
    (input : TraceLocalizationInput) :
    TraceCorQRepresentablePresheaf.inclusion.map
        input.generatorHom.representableObjectMap =
      input.map :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.Hom.representableObjectMap_inclusion
      input.generatorHom)
    (TraceLocalizationInput.generatorHom_representableMap input)

/-- The compact Yoneda preimage of the lifted input map is the input generator hom. -/
theorem TraceLocalizationInput.generatorHom_yonedaPreimage_representableObjectMap
    (input : TraceLocalizationInput) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        input.generatorHom.representableObjectMap =
      input.generatorHom :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
    input.generatorHom

end AnalyticMotives
end LFunctions
end Boundary
