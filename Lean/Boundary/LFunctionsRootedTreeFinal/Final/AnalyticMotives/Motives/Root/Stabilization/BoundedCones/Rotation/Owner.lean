import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Stabilization.BoundedCones.Rotation.Shift.Owner

/-!
# Motive-root rotated bounded cone facade

This file exposes rotated and inverse-rotated full bounded mapping-cone
triangles through the motive-root stabilization namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root facade: the rotated full bounded mapping-cone triangle. -/
def TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
    hom

/-- Motive-root facade: the rotated full bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_distinguished
    hom

/-- Motive-root facade: the inverse-rotated full bounded mapping-cone triangle. -/
def TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
    hom

/-- Motive-root facade: the inverse-rotated full bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_distinguished
    hom

/-- Motive-root facade: the first two morphisms of the rotated full bounded cone compose
to zero. -/
theorem TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle
      hom).mor₁ ≫
        (TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle
          hom).mor₂ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_first_comp_second
    hom

/-- Motive-root facade: the second and third morphisms of the rotated full bounded cone
compose to zero. -/
theorem TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle
      hom).mor₂ ≫
        (TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle
          hom).mor₃ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_second_comp_third
    hom

/-- Motive-root facade: the third morphism followed by the shifted first morphism of the
rotated full bounded cone is zero. -/
theorem TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle
      hom).mor₃ ≫
        ((TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle
          hom).mor₁)⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_third_comp_shifted_first
    hom

/-- Motive-root facade: the first two morphisms of the inverse-rotated full bounded cone
compose to zero. -/
theorem TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle
      hom).mor₁ ≫
        (TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle
          hom).mor₂ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_first_comp_second
    hom

/-- Motive-root facade: the second and third morphisms of the inverse-rotated full bounded
cone compose to zero. -/
theorem TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle
      hom).mor₂ ≫
        (TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle
          hom).mor₃ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_second_comp_third
    hom

/-- Motive-root facade: the third morphism followed by the shifted first morphism of the
inverse-rotated full bounded cone is zero. -/
theorem TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle
      hom).mor₃ ≫
        ((TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle
          hom).mor₁)⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_third_comp_shifted_first
    hom

end AnalyticMotives
end LFunctions
end Boundary
