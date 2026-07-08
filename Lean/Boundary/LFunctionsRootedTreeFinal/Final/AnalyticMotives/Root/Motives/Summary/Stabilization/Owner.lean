import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Stabilization.Owner

/-!
# Top-root stabilization summaries

This file exposes the stable additive-envelope homotopy category and its
triangulated structure under the public analytic-motives root namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public motive summary: the additive analytic homotopy category has a pretriangulated
structure. -/
def AnalyticMotivesRoot.rootSummary_pretriangulatedStructure :
    Pretriangulated TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootStabilization_pretriangulatedStructure

/-- Public motive summary: the additive analytic homotopy category is triangulated. -/
def AnalyticMotivesRoot.rootSummary_triangulatedStructure :
    IsTriangulated TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootStabilization_triangulatedStructure

/-- Public motive summary: the localized stable analytic motive category has shifts. -/
def AnalyticMotivesRoot.rootSummary_stableMotive_hasShiftStructure :
    HasShift TraceAnalyticStableMotiveCategory ℤ :=
  TraceAnalyticMotive.rootStableMotive_hasShiftStructure

/-- Public motive summary: the localized stable analytic motive category is
pretriangulated. -/
def AnalyticMotivesRoot.rootSummary_stableMotive_pretriangulatedStructure :
    Pretriangulated TraceAnalyticStableMotiveCategory :=
  TraceAnalyticMotive.rootStableMotive_pretriangulatedStructure

/-- Public motive summary: the localized stable analytic motive category is
triangulated. -/
def AnalyticMotivesRoot.rootSummary_stableMotive_triangulatedStructure :
    IsTriangulated TraceAnalyticStableMotiveCategory :=
  TraceAnalyticMotive.rootStableMotive_triangulatedStructure

/-- Public motive summary: distinguished triangles are Mathlib's distinguished triangles. -/
theorem AnalyticMotivesRoot.rootSummary_distinguishedTriangles_eq :
    TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles =
      Pretriangulated.distTriang TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootStabilization_distinguishedTriangles_eq

/-- Public motive summary: stable distinguished triangles are Mathlib's distinguished
triangles on the localized stable category. -/
theorem AnalyticMotivesRoot.rootSummary_stableMotive_distinguishedTriangles_eq :
    TraceAnalyticStableMotiveCategory.distinguishedTriangles =
      Pretriangulated.distTriang TraceAnalyticStableMotiveCategory :=
  TraceAnalyticMotive.rootStableMotive_distinguishedTriangles_eq

/-- Public motive summary: additive analytic mapping-cone triangles are distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_mappingCone_triangle_distinguished
    {source target : TraceAnalyticAdditiveCochainComplex}
    (hom : source ⟶ target) :
    CochainComplex.mappingCone.triangleh hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootStabilization_mappingCone_triangle_distinguished
    hom

/-- Public motive summary: a bounded analytic map has a full iso-bounded cone package. -/
def AnalyticMotivesRoot.rootSummary_boundedConePackage
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
      bound :=
  TraceAnalyticMotive.rootStabilization_boundedConePackage
    hom

/-- Public motive summary: bounded analytic cone packages are distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_boundedConePackage_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_boundedConePackage
      hom).trianglePackage.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootStabilization_boundedConePackage_distinguished
    hom

/-- Public motive summary: shifted bounded maps have full iso-bounded cone packages. -/
def AnalyticMotivesRoot.rootSummary_shiftedBoundedConePackage
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
      bound :=
  TraceAnalyticMotive.rootStabilization_shiftedBoundedConePackage
    hom
    shift

/-- Public motive summary: shifted bounded cone packages are distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedBoundedConePackage_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedBoundedConePackage
      hom
      shift).trianglePackage.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootStabilization_shiftedBoundedConePackage_distinguished
    hom
    shift

/-- Public motive summary: shifted bounded cone short complexes have zero composite. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedBoundedConeShortComplex_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
      hom
      shift).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
          hom
          shift).g =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedBoundedConeShortComplex_zero
    hom
    shift

/-- Public motive summary: the rotated full bounded cone triangle. -/
def AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle
    hom

/-- Public motive summary: the rotated full bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle_distinguished
    hom

/-- Public motive summary: the inverse-rotated full bounded cone triangle. -/
def AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle
    hom

/-- Public motive summary: the inverse-rotated full bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle hom ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle_distinguished
    hom

/-- Public motive summary: the first two morphisms of the rotated bounded cone compose to
zero. -/
theorem AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
      hom).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
          hom).mor₂ =
      0 :=
  TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle_first_comp_second
    hom

/-- Public motive summary: the second and third morphisms of the rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
      hom).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
          hom).mor₃ =
      0 :=
  TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle_second_comp_third
    hom

/-- Public motive summary: the third morphism followed by the shifted first morphism of
the rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
      hom).mor₃ ≫
        ((AnalyticMotivesRoot.rootSummary_rotatedBoundedConeTriangle
          hom).mor₁)⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootStabilization_rotatedBoundedConeTriangle_third_comp_shifted_first
    hom

/-- Public motive summary: the first two morphisms of the inverse-rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
      hom).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
          hom).mor₂ =
      0 :=
  TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle_first_comp_second
    hom

/-- Public motive summary: the second and third morphisms of the inverse-rotated bounded
cone compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
      hom).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
          hom).mor₃ =
      0 :=
  TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle_second_comp_third
    hom

/-- Public motive summary: the third morphism followed by the shifted first morphism of
the inverse-rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
      hom).mor₃ ≫
        ((AnalyticMotivesRoot.rootSummary_inverseRotatedBoundedConeTriangle
          hom).mor₁)⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootStabilization_inverseRotatedBoundedConeTriangle_third_comp_shifted_first
    hom

/-- Public motive summary: the rotated cone triangle of a shifted bounded map. -/
def AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle
    hom
    shift

/-- Public motive summary: the shifted rotated bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle hom shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle_distinguished
    hom
    shift

/-- Public motive summary: the inverse-rotated cone triangle of a shifted bounded map. -/
def AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle
    hom
    shift

/-- Public motive summary: the shifted inverse-rotated bounded cone triangle is
distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle hom shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle_distinguished
    hom
    shift

/-- Public motive summary: the first two morphisms of the shifted rotated bounded cone
compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₂ =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle_first_comp_second
    hom
    shift

/-- Public motive summary: the second and third morphisms of the shifted rotated bounded
cone compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₃ =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle_second_comp_third
    hom
    shift

/-- Public motive summary: the third morphism followed by the shifted first morphism of
the shifted rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
      hom
      shift).mor₃ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedRotatedBoundedConeTriangle
          hom
          shift).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedRotatedBoundedConeTriangle_third_comp_shifted_first
    hom
    shift

/-- Public motive summary: the first two morphisms of the shifted inverse-rotated bounded
cone compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₁ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₂ =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle_first_comp_second
    hom
    shift

/-- Public motive summary: the second and third morphisms of the shifted inverse-rotated
bounded cone compose to zero. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₂ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₃ =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle_second_comp_third
    hom
    shift

/-- Public motive summary: the third morphism followed by the shifted first morphism of
the shifted inverse-rotated bounded cone is zero. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
      hom
      shift).mor₃ ≫
        (AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedBoundedConeTriangle
          hom
          shift).mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedBoundedConeTriangle_third_comp_shifted_first
    hom
    shift

/-- Public motive summary: in a shifted rotated cone, cone inclusion followed by
connecting map is zero. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedRotatedCone_secondMap_comp_connectingMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (hom.shift shift) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (hom.shift shift) =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedRotatedCone_secondMap_comp_connectingMap
    hom
    shift

/-- Public motive summary: in a shifted rotated cone, connecting map followed by the
negative shifted bounded map is zero. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedRotatedCone_connectingMap_comp_negative_shifted_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (hom.shift shift) ≫
        -((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift))⟦(1 : ℤ)⟧') =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedRotatedCone_connectingMap_comp_negative_shifted_firstMap
    hom
    shift

/-- Public motive summary: in a shifted inverse-rotated cone, shifted negative connecting
map followed by the shifted bounded map is zero. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedCone_negative_shifted_connectingMap_comp_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (-(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (hom.shift shift))⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift) =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedCone_negative_shifted_connectingMap_comp_firstMap
    hom
    shift

/-- Public motive summary: in a shifted inverse-rotated cone, shifted bounded map followed
by transported cone inclusion is zero. -/
theorem AnalyticMotivesRoot.rootSummary_shiftedInverseRotatedCone_firstMap_comp_transport_secondMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (hom.shift shift) ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).counitIso.inv.app _ =
      0 :=
  TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedCone_firstMap_comp_transport_secondMap
    hom
    shift

end AnalyticMotives
end LFunctions
end Boundary
