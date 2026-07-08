import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.TateStabilization.Owner

/-!
# Public Tate rotated-cone exactness facade

This file exposes the Tate weight-drop rotated and inverse-rotated bounded
mapping-cone exactness equations at the top root surface.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public root summary: the first two morphisms of the Tate rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_first_comp_second
    source
    target

/-- Public root summary: the second and third morphisms of the Tate rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_second_comp_third
    source
    target

/-- Public root summary: the third morphism followed by the shifted first morphism of
the Tate rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    source
    target

/-- Public root summary: the first two morphisms of the Tate inverse-rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_first_comp_second
    source
    target

/-- Public root summary: the second and third morphisms of the Tate inverse-rotated
bounded cone compose to zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_second_comp_third
    source
    target

/-- Public root summary: the third morphism followed by the shifted first morphism of
the Tate inverse-rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
