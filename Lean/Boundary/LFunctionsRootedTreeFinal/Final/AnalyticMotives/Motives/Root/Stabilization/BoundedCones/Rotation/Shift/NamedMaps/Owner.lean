import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Rotation.Maps.Exactness.Owner

/-!
# Motive-root named-map exactness for shifted rotated cones

This file exposes the exactness of shifted rotated mapping-cone triangles in
terms of the named cone maps: bounded map, cone inclusion, and connecting map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root facade: in a shifted rotated cone, cone inclusion followed by connecting
map is zero. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedRotatedCone_secondMap_comp_connectingMap
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
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_secondMap_comp_connectingMap
    hom
    shift

/-- Motive-root facade: in a shifted rotated cone, connecting map followed by the negative
shifted bounded map is zero. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedRotatedCone_connectingMap_comp_negative_shifted_firstMap
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
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_connectingMap_comp_negative_shifted_firstMap
    hom
    shift

/-- Motive-root facade: in a shifted inverse-rotated cone, the shifted negative connecting
map followed by the shifted bounded map is zero. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedCone_negative_shifted_connectingMap_comp_firstMap
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
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_negative_shifted_connectingMap_comp_firstMap
    hom
    shift

/-- Motive-root facade: in a shifted inverse-rotated cone, the shifted bounded map followed
by the transported cone inclusion is zero. -/
theorem TraceAnalyticMotive.rootStabilization_shiftedInverseRotatedCone_firstMap_comp_transport_secondMap
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
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_firstMap_comp_transport_secondMap
    hom
    shift

end AnalyticMotives
end LFunctions
end Boundary
