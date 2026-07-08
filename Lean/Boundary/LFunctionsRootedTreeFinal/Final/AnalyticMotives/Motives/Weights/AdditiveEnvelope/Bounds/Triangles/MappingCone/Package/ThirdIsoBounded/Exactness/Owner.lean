import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.ThirdIsoBounded.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Owner

/-!
# Exactness of full bounded mapping-cone packages

The full mapping-cone package with third iso-bounded data still carries the
standard exactness identities of its underlying distinguished triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The first two morphisms of the full mapping-cone package compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
      hom).trianglePackage.triangle.mor₁ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
          hom).trianglePackage.triangle.mor₂ =
      0 :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
    hom).first_comp_second

/-- The second and third morphisms of the full mapping-cone package compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
      hom).trianglePackage.triangle.mor₂ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
          hom).trianglePackage.triangle.mor₃ =
      0 :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
    hom).second_comp_third

/-- The third morphism followed by the shifted first morphism is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
      hom).trianglePackage.triangle.mor₃ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
          hom).trianglePackage.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
    hom).third_comp_shifted_first

end AnalyticMotives
end LFunctions
end Boundary
