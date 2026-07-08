import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Rotation.Maps.Owner

/-!
# Exactness for rotations of shifted-map mapping-cone triangles

The rotated and inverse-rotated mapping-cone triangles of `hom.shift n` carry
the three standard zero-composite identities of distinguished triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

/-- The first two morphisms of the shifted-map rotated triangle compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift).mor₁ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
          hom
          shift).mor₂ =
      0 :=
  comp_distTriang_mor_zero₁₂
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_distinguished
      hom
      shift)

/-- The second and third morphisms of the shifted-map rotated triangle compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift).mor₂ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
          hom
          shift).mor₃ =
      0 :=
  comp_distTriang_mor_zero₂₃
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_distinguished
      hom
      shift)

/-- The third morphism of the shifted-map rotated triangle followed by the shifted first
morphism is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift).mor₃ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
          hom
          shift).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  comp_distTriang_mor_zero₃₁
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
      hom
      shift)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_distinguished
      hom
      shift)

/-- The first two morphisms of the shifted-map inverse-rotated triangle compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift).mor₁ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
          hom
          shift).mor₂ =
      0 :=
  comp_distTriang_mor_zero₁₂
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_distinguished
      hom
      shift)

/-- The second and third morphisms of the shifted-map inverse-rotated triangle compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift).mor₂ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
          hom
          shift).mor₃ =
      0 :=
  comp_distTriang_mor_zero₂₃
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_distinguished
      hom
      shift)

/-- The third morphism of the shifted-map inverse-rotated triangle followed by the shifted
first morphism is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift).mor₃ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
          hom
          shift).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  comp_distTriang_mor_zero₃₁
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
      hom
      shift)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_distinguished
      hom
      shift)

end AnalyticMotives
end LFunctions
end Boundary
