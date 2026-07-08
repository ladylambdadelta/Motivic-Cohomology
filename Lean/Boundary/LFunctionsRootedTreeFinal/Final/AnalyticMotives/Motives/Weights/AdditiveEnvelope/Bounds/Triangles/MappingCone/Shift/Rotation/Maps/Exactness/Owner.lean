import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Rotation.Exactness.Owner

/-!
# Named-map exactness for rotations of shifted-map cones

The exactness identities for the rotated and inverse-rotated mapping-cone
triangles of `hom.shift n` are exposed in terms of the named cone maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- In the shifted-map rotated triangle, the cone inclusion followed by the connecting map
is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_secondMap_comp_connectingMap
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
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_first_comp_second
    hom
    shift

/-- In the shifted-map rotated triangle, the connecting map followed by the negative shifted
bounded map is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_connectingMap_comp_negative_shifted_firstMap
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
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_second_comp_third
    hom
    shift

/-- In the shifted-map inverse-rotated triangle, the shifted negative connecting map followed
by the shifted bounded map is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_negative_shifted_connectingMap_comp_firstMap
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
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_first_comp_second
    hom
    shift

/-- In the shifted-map inverse-rotated triangle, the shifted bounded map followed by the
transported cone inclusion is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_firstMap_comp_transport_secondMap
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
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_second_comp_third
    hom
    shift

end AnalyticMotives
end LFunctions
end Boundary
