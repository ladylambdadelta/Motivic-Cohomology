import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Rotation.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Stabilization.BoundedCones.Rotation.Shift.NamedMaps.Owner

/-!
# Motive-root shifted rotated bounded cone facade

This file exposes the rotated and inverse-rotated mapping-cone triangles of
shifted bounded maps through the motive-root stabilization namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root facade: the rotated mapping-cone triangle of a shifted bounded map. -/
def TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
    hom
    shift

/-- Motive-root facade: the shifted rotated bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle hom shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_distinguished
    hom
    shift

/-- Motive-root facade: the inverse-rotated mapping-cone triangle of a shifted bounded map. -/
def TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
    hom
    shift

/-- Motive-root facade: the shifted inverse-rotated bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle hom shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_distinguished
    hom
    shift

/-- Motive-root facade: the first two morphisms of the shifted rotated bounded cone compose
to zero. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₁ ≫
        (TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₂ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_first_comp_second
    hom
    shift

/-- Motive-root facade: the second and third morphisms of the shifted rotated bounded cone
compose to zero. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₂ ≫
        (TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₃ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_second_comp_third
    hom
    shift

/-- Motive-root facade: the third morphism followed by the shifted first morphism of the
shifted rotated bounded cone is zero. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₃ ≫
        (TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_third_comp_shifted_first
    hom
    shift

/-- Motive-root facade: the first two morphisms of the shifted inverse-rotated bounded cone
compose to zero. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₁ ≫
        (TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₂ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_first_comp_second
    hom
    shift

/-- Motive-root facade: the second and third morphisms of the shifted inverse-rotated
bounded cone compose to zero. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₂ ≫
        (TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₃ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_second_comp_third
    hom
    shift

/-- Motive-root facade: the third morphism followed by the shifted first morphism of the
shifted inverse-rotated bounded cone is zero. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₃ ≫
        (TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_third_comp_shifted_first
    hom
    shift

end AnalyticMotives
end LFunctions
end Boundary
