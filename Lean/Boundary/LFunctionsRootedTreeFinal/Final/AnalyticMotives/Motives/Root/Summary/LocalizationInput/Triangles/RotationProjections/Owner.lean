import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Rotation.Projections.Owner

/-!
# Motive-root localization-input rotated cone triangle projections

This file exposes vertex and morphism projections for rotated and
inverse-rotated localization-input bounded cone triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root summary: the rotated triangle has target as first vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_obj₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₁
    input

/-- Motive-root summary: the rotated triangle has cone as second vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_obj₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₂
    input

/-- Motive-root summary: the rotated triangle has shifted source as third vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_obj₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.obj₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧ :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₃
    input

/-- Motive-root summary: the first rotated triangle morphism is cone inclusion. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_mor₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₁
    input

/-- Motive-root summary: the second rotated triangle morphism is the connecting map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_mor₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₂
    input

/-- Motive-root summary: the third rotated triangle morphism is the negative shifted
bounded map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeRotatedTriangle_mor₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₃ =
      -((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧') :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₃
    input

/-- Motive-root summary: the inverse-rotated triangle has shifted cone as first vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_obj₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.obj₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧ :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₁
    input

/-- Motive-root summary: the inverse-rotated triangle has source as second vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_obj₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₂
    input

/-- Motive-root summary: the inverse-rotated triangle has target as third vertex. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_obj₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.obj₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₃
    input

/-- Motive-root summary: the first inverse-rotated morphism is the shifted negative
connecting map with unit transport. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_mor₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₁ =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₁
    input

/-- Motive-root summary: the second inverse-rotated morphism is the bounded map. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_mor₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₂
    input

/-- Motive-root summary: the third inverse-rotated morphism is cone inclusion with
counit transport. -/
theorem TraceAnalyticMotive.rootSummary_localizationInput_boundedMappingConeInverseRotatedTriangle_mor₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₃
    input

end AnalyticMotives
end LFunctions
end Boundary
