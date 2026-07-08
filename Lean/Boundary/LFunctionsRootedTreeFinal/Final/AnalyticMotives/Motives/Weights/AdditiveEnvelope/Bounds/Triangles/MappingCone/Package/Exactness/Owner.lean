import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.Owner

/-!
# Exactness of packaged bounded mapping-cone triangles

A bounded analytic chain map generates a packaged bounded distinguished
triangle, and its three consecutive triangle composites vanish.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The first two morphisms in a bounded mapping-cone triangle compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
      hom).triangle.mor₁ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
          hom).triangle.mor₂ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.first_comp_second
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
      hom)

/-- The second and third morphisms in a bounded mapping-cone triangle compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
      hom).triangle.mor₂ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
          hom).triangle.mor₃ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.second_comp_third
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
      hom)

/-- The third morphism followed by the shifted first morphism is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
      hom).triangle.mor₃ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
          hom).triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.third_comp_shifted_first
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
      hom)

end AnalyticMotives
end LFunctions
end Boundary
