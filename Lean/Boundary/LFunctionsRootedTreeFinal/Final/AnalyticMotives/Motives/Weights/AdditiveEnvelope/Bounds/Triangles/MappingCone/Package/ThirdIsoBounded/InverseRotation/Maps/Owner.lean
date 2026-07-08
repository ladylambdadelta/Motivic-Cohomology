import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Rotation.Owner

/-!
# Maps in inverse-rotated full bounded mapping-cone packages

The inverse-rotated full bounded mapping-cone triangle exposes Mathlib's
standard inverse-rotation formula in terms of the named cone maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first vertex of the inverse-rotated package triangle is the cone shifted by `-1`. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_obj₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom).obj₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        hom)⟦(-1 : ℤ)⟧ :=
  rfl

/-- The second vertex of the inverse-rotated package triangle is the bounded source object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_obj₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom).obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject hom :=
  rfl

/-- The third vertex of the inverse-rotated package triangle is the bounded target object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_obj₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom).obj₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject hom :=
  rfl

/-- The first inverse-rotated morphism is the shifted negative connecting map with unit transport. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_mor₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom).mor₁ =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        hom)⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  rfl

/-- The second inverse-rotated morphism is the bounded map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_mor₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom).mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap hom :=
  rfl

/-- The third inverse-rotated morphism is the cone inclusion with counit transport. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_mor₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom).mor₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap hom ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
