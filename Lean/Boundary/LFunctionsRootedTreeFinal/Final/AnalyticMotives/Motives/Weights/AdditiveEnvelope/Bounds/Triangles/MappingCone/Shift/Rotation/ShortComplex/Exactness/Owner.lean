import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Rotation.Maps.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Rotation.ShortComplex.Projections.Owner

/-!
# Named exactness for rotated short complexes of shifted-map cones

The zero composites in the rotated and inverse-rotated shifted-map short
complexes are exposed through the named-map exactness theorems for the
corresponding rotated triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The shifted-map rotated short complex has zero composite by named cone-map exactness. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex_named_zero
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

/-- The shifted-map inverse-rotated short complex has zero composite by named cone-map
exactness. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex_named_zero
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

/-- The rotated short-complex zero composite is the named cone-map exactness theorem. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex_zero_eq_named_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex
      hom
      shift).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex
          hom
          shift).g =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedShortComplex_named_zero
    hom
    shift

/-- The inverse-rotated short-complex zero composite is the named cone-map exactness theorem. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex_zero_eq_named_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex
      hom
      shift).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex
          hom
          shift).g =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedShortComplex_named_zero
    hom
    shift

end AnalyticMotives
end LFunctions
end Boundary
