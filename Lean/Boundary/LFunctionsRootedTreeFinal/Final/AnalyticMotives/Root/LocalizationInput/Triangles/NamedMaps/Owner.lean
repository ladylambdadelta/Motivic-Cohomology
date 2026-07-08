import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.Triangles.NamedMaps.Owner

/-!
# Public localization-input cone named-map exactness facade

This file exposes named-map exactness laws for arbitrary localization-input
bounded cones at the top root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public root facade: the bounded map followed by cone inclusion is zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedCone_firstMap_comp_secondMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          input.boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          input.boundedAdditiveComplexHom =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedCone_firstMap_comp_secondMap
    input

/-- Public root facade: cone inclusion followed by the connecting map is zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedCone_secondMap_comp_connectingMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          input.boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          input.boundedAdditiveComplexHom =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedCone_secondMap_comp_connectingMap
    input

/-- Public root facade: the connecting map followed by the shifted bounded map is zero. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedCone_connectingMap_comp_shifted_firstMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          input.boundedAdditiveComplexHom ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedCone_connectingMap_comp_shifted_firstMap
    input

end AnalyticMotives
end LFunctions
end Boundary
