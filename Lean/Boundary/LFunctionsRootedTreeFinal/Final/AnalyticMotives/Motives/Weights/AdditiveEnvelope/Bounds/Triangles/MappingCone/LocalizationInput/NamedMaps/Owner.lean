import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Maps.Exactness.Owner

/-!
# Named-map exactness for localization-input bounded cones

This file states the localization-input cone exactness laws using the named
bounded map, cone-inclusion map, and connecting map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localization-input bounded map followed by its cone-inclusion map is zero. -/
theorem TraceLocalizationInput.boundedMappingCone_firstMap_comp_secondMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          input.boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          input.boundedAdditiveComplexHom =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.first_comp_secondMap
    input.boundedAdditiveComplexHom

/-- The localization-input cone-inclusion map followed by its connecting map is zero. -/
theorem TraceLocalizationInput.boundedMappingCone_secondMap_comp_connectingMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          input.boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          input.boundedAdditiveComplexHom =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap_comp_connectingMap
    input.boundedAdditiveComplexHom

/-- The localization-input connecting map followed by the shifted bounded map is zero. -/
theorem TraceLocalizationInput.boundedMappingCone_connectingMap_comp_shifted_firstMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          input.boundedAdditiveComplexHom ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap_comp_shifted_firstMap
    input.boundedAdditiveComplexHom

end AnalyticMotives
end LFunctions
end Boundary
