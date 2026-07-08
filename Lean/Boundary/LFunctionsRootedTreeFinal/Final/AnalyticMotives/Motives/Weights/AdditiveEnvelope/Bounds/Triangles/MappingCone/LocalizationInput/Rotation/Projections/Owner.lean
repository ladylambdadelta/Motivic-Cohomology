import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.InverseRotation.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Rotation.Maps.Owner

/-!
# Projections of localization-input rotated bounded mapping-cone triangles

This file specializes rotated and inverse-rotated full bounded mapping-cone
vertex and morphism projections to localization-input bounded maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first vertex of the localization-input rotated triangle is the target object. -/
theorem TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_obj₁
    input.boundedAdditiveComplexHom

/-- The second vertex of the localization-input rotated triangle is the cone object. -/
theorem TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_obj₂
    input.boundedAdditiveComplexHom

/-- The third vertex of the localization-input rotated triangle is the shifted source
object. -/
theorem TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.obj₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧ :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_obj₃
    input.boundedAdditiveComplexHom

/-- The first morphism of the localization-input rotated triangle is cone inclusion. -/
theorem TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_mor₁
    input.boundedAdditiveComplexHom

/-- The second morphism of the localization-input rotated triangle is the connecting
map. -/
theorem TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_mor₂
    input.boundedAdditiveComplexHom

/-- The third morphism of the localization-input rotated triangle is the negative
shifted bounded map. -/
theorem TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeRotatedTriangle.mor₃ =
      -((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom)⟦(1 : ℤ)⟧') :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_mor₃
    input.boundedAdditiveComplexHom

/-- The first vertex of the localization-input inverse-rotated triangle is the shifted
cone object. -/
theorem TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.obj₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧ :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_obj₁
    input.boundedAdditiveComplexHom

/-- The second vertex of the localization-input inverse-rotated triangle is the source
object. -/
theorem TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_obj₂
    input.boundedAdditiveComplexHom

/-- The third vertex of the localization-input inverse-rotated triangle is the target
object. -/
theorem TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.obj₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        input.boundedAdditiveComplexHom :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_obj₃
    input.boundedAdditiveComplexHom

/-- The first morphism of the localization-input inverse-rotated triangle is the shifted
negative connecting map with unit transport. -/
theorem TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₁
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₁ =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        input.boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_mor₁
    input.boundedAdditiveComplexHom

/-- The second morphism of the localization-input inverse-rotated triangle is the
bounded map. -/
theorem TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₂
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        input.boundedAdditiveComplexHom :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_mor₂
    input.boundedAdditiveComplexHom

/-- The third morphism of the localization-input inverse-rotated triangle is cone
inclusion with counit transport. -/
theorem TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₃
    (input : TraceLocalizationInput) :
    input.boundedMappingConeInverseRotatedTriangle.mor₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        input.boundedAdditiveComplexHom ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_mor₃
    input.boundedAdditiveComplexHom

end AnalyticMotives
end LFunctions
end Boundary
