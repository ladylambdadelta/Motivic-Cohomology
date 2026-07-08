import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.InverseRotation.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Rotation.Maps.Owner

/-!
# Exactness of rotated full bounded mapping-cone packages

Rotated and inverse-rotated full bounded mapping-cone triangles are
distinguished triangles, hence their consecutive triangle morphisms compose to
zero.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

/-- The first two morphisms of the rotated full package compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom).mor₁ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
          hom).mor₂ =
      0 :=
  comp_distTriang_mor_zero₁₂
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_distinguished
      hom)

/-- The second and third morphisms of the rotated full package compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom).mor₂ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
          hom).mor₃ =
      0 :=
  comp_distTriang_mor_zero₂₃
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_distinguished
      hom)

/-- The third morphism followed by the shifted first morphism in the rotated full package
is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom).mor₃ ≫
        ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
          hom).mor₁)⟦(1 : ℤ)⟧' =
      0 :=
  comp_distTriang_mor_zero₃₁
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_distinguished
      hom)

/-- The first two morphisms of the inverse-rotated full package compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom).mor₁ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
          hom).mor₂ =
      0 :=
  comp_distTriang_mor_zero₁₂
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_distinguished
      hom)

/-- The second and third morphisms of the inverse-rotated full package compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom).mor₂ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
          hom).mor₃ =
      0 :=
  comp_distTriang_mor_zero₂₃
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_distinguished
      hom)

/-- The third morphism followed by the shifted first morphism in the inverse-rotated full
package is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom).mor₃ ≫
        ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
          hom).mor₁)⟦(1 : ℤ)⟧' =
      0 :=
  comp_distTriang_mor_zero₃₁
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_distinguished
      hom)

end AnalyticMotives
end LFunctions
end Boundary
