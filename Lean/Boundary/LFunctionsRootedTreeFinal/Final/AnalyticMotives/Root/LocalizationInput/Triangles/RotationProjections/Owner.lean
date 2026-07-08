import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.Triangles.RotationProjections.Owner

/-!
# Public localization-input rotated cone triangle projection facade

This file exposes vertex and morphism projections for rotated and
inverse-rotated localization-input bounded cone triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public root facade: the rotated triangle has target as first vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle_obj₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_obj₁
    input

/-- Public root facade: the rotated triangle has cone as second vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle_obj₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_obj₂
    input

/-- Public root facade: the rotated triangle has shifted source as third vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle_obj₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.obj₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧ :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_obj₃
    input

/-- Public root facade: the first rotated triangle morphism is cone inclusion. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle_mor₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_mor₁
    input

/-- Public root facade: the second rotated triangle morphism is the connecting map. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle_mor₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_mor₂
    input

/-- Public root facade: the third rotated triangle morphism is the negative shifted
bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeRotatedTriangle_mor₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₃ =
      -((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧') :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_mor₃
    input

/-- Public root facade: the inverse-rotated triangle has shifted cone as first vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle_obj₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.obj₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧ :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_obj₁
    input

/-- Public root facade: the inverse-rotated triangle has source as second vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle_obj₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_obj₂
    input

/-- Public root facade: the inverse-rotated triangle has target as third vertex. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle_obj₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.obj₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_obj₃
    input

/-- Public root facade: the first inverse-rotated morphism is the shifted negative
connecting map with unit transport. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle_mor₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₁ =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_mor₁
    input

/-- Public root facade: the second inverse-rotated morphism is the bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle_mor₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_mor₂
    input

/-- Public root facade: the third inverse-rotated morphism is cone inclusion with counit
transport. -/
theorem AnalyticMotivesRoot.rootFacade_localizationInput_boundedMappingConeInverseRotatedTriangle_mor₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  AnalyticMotivesRoot.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_mor₃
    input

end AnalyticMotives
end LFunctions
end Boundary
