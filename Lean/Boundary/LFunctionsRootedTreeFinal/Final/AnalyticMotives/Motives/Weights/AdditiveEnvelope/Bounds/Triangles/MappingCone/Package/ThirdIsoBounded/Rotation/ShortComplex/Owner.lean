import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Rotation.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Monotone.Owner

/-!
# Short complexes from rotated full bounded mapping-cone packages

The rotated full bounded mapping-cone triangle carries the short complex formed
by the cone inclusion and the connecting morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

/-- The short complex attached to the rotated full bounded mapping-cone triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  shortComplexOfDistTriangle
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
      hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_distinguished
      hom)

/-- The left vertex of the rotated short complex is the target object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex_X₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex
      hom).X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject hom :=
  rfl

/-- The middle vertex of the rotated short complex is the cone object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex_X₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex
      hom).X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject hom :=
  rfl

/-- The right vertex of the rotated short complex is the shifted source object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex_X₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex
      hom).X₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        hom)⟦(1 : ℤ)⟧ :=
  rfl

/-- The first morphism of the rotated short complex is the cone inclusion. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex_f
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex
      hom).f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap hom :=
  rfl

/-- The second morphism of the rotated short complex is the connecting map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex_g
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex
      hom).g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap hom :=
  rfl

/-- The cone inclusion followed by the connecting map is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex
      hom).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex
          hom).g =
      0 :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex
    hom).zero

/-- Rebounding the weight bound preserves the rotated short complex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rebound_rotatedShortComplex
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    shortComplexOfDistTriangle
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rebound
          bound_le
          hom).rotatedTriangle
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rebound
          bound_le
          hom).rotatedTriangle_distinguished =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedShortComplex
        hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
