import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.NamedMaps.Owner

/-!
# Motive-root localization-input cone named-map exactness

This file exposes the named bounded-map, cone-inclusion, and connecting-map
exactness laws for arbitrary localization-input bounded cones.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: the bounded map followed by cone inclusion is zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedCone_firstMap_comp_secondMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          input.boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          input.boundedAdditiveComplexHom =
      0 :=
  TraceLocalizationInput.boundedMappingCone_firstMap_comp_secondMap
    input

/-- Motive-root summary: cone inclusion followed by the connecting map is zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedCone_secondMap_comp_connectingMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          input.boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          input.boundedAdditiveComplexHom =
      0 :=
  TraceLocalizationInput.boundedMappingCone_secondMap_comp_connectingMap
    input

/-- Motive-root summary: the connecting map followed by the shifted bounded map is
zero. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedCone_connectingMap_comp_shifted_firstMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          input.boundedAdditiveComplexHom ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingCone_connectingMap_comp_shifted_firstMap
    input

end AnalyticMotives
end LFunctions
end Boundary
