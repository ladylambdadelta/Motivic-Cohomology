import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Rotation.ShortComplex.Owner

/-!
# Projections for rotated short complexes of shifted-map cones

This file exposes the vertices, maps, and zero composites of the rotated and
inverse-rotated short complexes attached to the mapping cone of `hom.shift n`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The left vertex of the shifted-map rotated short complex is the shifted target object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex_X₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex
      hom
      shift).X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (hom.shift shift) :=
  rfl

/-- The middle vertex of the shifted-map rotated short complex is the shifted-map cone object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex_X₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex
      hom
      shift).X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (hom.shift shift) :=
  rfl

/-- The right vertex of the shifted-map rotated short complex is the shifted source object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex_X₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex
      hom
      shift).X₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (hom.shift shift))⟦(1 : ℤ)⟧ :=
  rfl

/-- The first map of the shifted-map rotated short complex is the cone inclusion. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex_f
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex
      hom
      shift).f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (hom.shift shift) :=
  rfl

/-- The second map of the shifted-map rotated short complex is the connecting map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex_g
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex
      hom
      shift).g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (hom.shift shift) :=
  rfl

/-- The first two maps of the shifted-map rotated short complex compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex
      hom
      shift).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex
          hom
          shift).g =
      0 :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex
    hom
    shift).zero

/-- The left vertex of the shifted-map inverse-rotated short complex is the shifted-map cone
shifted by `-1`. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex_X₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex
      hom
      shift).X₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (hom.shift shift))⟦(-1 : ℤ)⟧ :=
  rfl

/-- The middle vertex of the shifted-map inverse-rotated short complex is the shifted source. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex_X₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex
      hom
      shift).X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (hom.shift shift) :=
  rfl

/-- The right vertex of the shifted-map inverse-rotated short complex is the shifted target. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex_X₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex
      hom
      shift).X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (hom.shift shift) :=
  rfl

/-- The first map of the shifted-map inverse-rotated short complex is the shifted negative
connecting map with unit transport. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex_f
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex
      hom
      shift).f =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (hom.shift shift))⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  rfl

/-- The second map of the shifted-map inverse-rotated short complex is the shifted map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex_g
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex
      hom
      shift).g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (hom.shift shift) :=
  rfl

/-- The first two maps of the shifted-map inverse-rotated short complex compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex
      hom
      shift).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex
          hom
          shift).g =
      0 :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex
    hom
    shift).zero

end AnalyticMotives
end LFunctions
end Boundary
