import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.InverseRotation.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Monotone.Owner

/-!
# Short complexes from inverse-rotated full bounded mapping-cone packages

The inverse-rotated full bounded mapping-cone triangle carries the short
complex formed by the shifted negative connecting map and the bounded map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

/-- The short complex attached to the inverse-rotated full bounded mapping-cone triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  shortComplexOfDistTriangle
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
      hom)
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_distinguished
      hom)

/-- The left vertex of the inverse-rotated short complex is the cone shifted by `-1`. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex_X₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex
      hom).X₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        hom)⟦(-1 : ℤ)⟧ :=
  rfl

/-- The middle vertex of the inverse-rotated short complex is the source object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex_X₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex
      hom).X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject hom :=
  rfl

/-- The right vertex of the inverse-rotated short complex is the target object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex_X₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex
      hom).X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject hom :=
  rfl

/-- The first morphism is the shifted negative connecting map with unit transport. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex_f
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex
      hom).f =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        hom)⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  rfl

/-- The second morphism is the bounded map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex_g
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex
      hom).g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap hom :=
  rfl

/-- The first two morphisms of the inverse-rotated short complex compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex
      hom).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex
          hom).g =
      0 :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex
    hom).zero

/-- Rebounding the weight bound preserves the inverse-rotated short complex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rebound_inverseRotatedShortComplex
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    shortComplexOfDistTriangle
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rebound
          bound_le
          hom).inverseRotatedTriangle
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rebound
          bound_le
          hom).inverseRotatedTriangle_distinguished =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedShortComplex
        hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
