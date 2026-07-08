import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.Triangles.NamedMaps.Owner

/-!
# Top-root localization-input cone named-map exactness

This file exposes named-map exactness laws for arbitrary localization-input
bounded cones under the public root namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public motive summary: the bounded map followed by cone inclusion is zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedCone_firstMap_comp_secondMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          input.boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          input.boundedAdditiveComplexHom =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedCone_firstMap_comp_secondMap
    input

/-- Public motive summary: cone inclusion followed by the connecting map is zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedCone_secondMap_comp_connectingMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          input.boundedAdditiveComplexHom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          input.boundedAdditiveComplexHom =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedCone_secondMap_comp_connectingMap
    input

/-- Public motive summary: the connecting map followed by the shifted bounded map is
zero. -/
theorem AnalyticMotivesRoot.rootSummary_localizationInput_boundedCone_connectingMap_comp_shifted_firstMap
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          input.boundedAdditiveComplexHom ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootSummary_localizationInput_boundedCone_connectingMap_comp_shifted_firstMap
    input

end AnalyticMotives
end LFunctions
end Boundary
