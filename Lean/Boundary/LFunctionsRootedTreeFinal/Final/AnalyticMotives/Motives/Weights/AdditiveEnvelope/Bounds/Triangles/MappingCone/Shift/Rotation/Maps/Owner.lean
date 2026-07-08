import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.InverseRotation.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Rotation.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Rotation.Owner

/-!
# Maps in rotations of shifted-map mapping-cone triangles

The vertices and morphisms of the rotated and inverse-rotated mapping-cone
triangles of `hom.shift n` are the existing mapping-cone rotation formulas
applied to the shifted bounded map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first vertex of the shifted-map rotated triangle is the shifted target object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_obj₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift).obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (hom.shift shift) :=
  rfl

/-- The second vertex of the shifted-map rotated triangle is the shifted-map cone object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_obj₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift).obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (hom.shift shift) :=
  rfl

/-- The third vertex of the shifted-map rotated triangle is the shifted source object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_obj₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift).obj₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (hom.shift shift))⟦(1 : ℤ)⟧ :=
  rfl

/-- The first morphism of the shifted-map rotated triangle is the cone inclusion. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_mor₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift).mor₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (hom.shift shift) :=
  rfl

/-- The second morphism of the shifted-map rotated triangle is the connecting map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_mor₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift).mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (hom.shift shift) :=
  rfl

/-- The third morphism of the shifted-map rotated triangle is the negative shifted map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_mor₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift).mor₃ =
      -((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (hom.shift shift))⟦(1 : ℤ)⟧') :=
  rfl

/-- The first vertex of the shifted-map inverse-rotated triangle is the shifted-map cone
shifted by `-1`. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_obj₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift).obj₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (hom.shift shift))⟦(-1 : ℤ)⟧ :=
  rfl

/-- The second vertex of the shifted-map inverse-rotated triangle is the shifted source. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_obj₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift).obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (hom.shift shift) :=
  rfl

/-- The third vertex of the shifted-map inverse-rotated triangle is the shifted target. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_obj₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift).obj₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (hom.shift shift) :=
  rfl

/-- The first morphism of the shifted-map inverse-rotated triangle is the shifted negative
connecting map with unit transport. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_mor₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift).mor₁ =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (hom.shift shift))⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  rfl

/-- The second morphism of the shifted-map inverse-rotated triangle is the shifted bounded map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_mor₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift).mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (hom.shift shift) :=
  rfl

/-- The third morphism of the shifted-map inverse-rotated triangle is the cone inclusion
with counit transport. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_mor₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift).mor₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (hom.shift shift) ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
