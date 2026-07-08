import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Rotation.Owner

/-!
# Maps in rotated full bounded mapping-cone packages

The rotated full bounded mapping-cone triangle has the cone inclusion as its
first morphism, the connecting morphism as its second morphism, and the
negative shifted bounded map as its third morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The first vertex of the rotated package triangle is the bounded target object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_obj₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom).obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject hom :=
  rfl

/-- The second vertex of the rotated package triangle is the cone object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_obj₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom).obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject hom :=
  rfl

/-- The third vertex of the rotated package triangle is the shifted source object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_obj₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom).obj₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        hom)⟦(1 : ℤ)⟧ :=
  rfl

/-- The first morphism of the rotated package triangle is the cone inclusion. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_mor₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom).mor₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap hom :=
  rfl

/-- The second morphism of the rotated package triangle is the connecting map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_mor₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom).mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap hom :=
  rfl

/-- The third morphism of the rotated package triangle is the negative shifted bounded map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_mor₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom).mor₃ =
      -((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        hom)⟦(1 : ℤ)⟧') :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
