import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.ShortComplex.Owner

/-!
# Comparing shifted mapping-cone short complexes

The short complex attached to the shifted original mapping-cone triangle is
isomorphic to the short complex attached to the mapping-cone triangle of the
shifted bounded map, using Mathlib's shifted mapping-cone triangle isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

/-- The short complex attached directly to the shifted original mapping-cone triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  shortComplexOfDistTriangle
    ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
      hom).shiftedTriangle
      shift)
    ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
      hom).shiftedTriangle_distinguished
      shift)

/-- The target short complex obtained by transporting distinguishedness along the
shifted mapping-cone triangle isomorphism. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  shortComplexOfDistTriangle
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
      (hom.shift shift))
    (isomorphic_distinguished
      _
      ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
        hom).shiftedTriangle_distinguished
        shift)
      _
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
        hom
        shift).symm)

/-- The shifted original cone short complex is isomorphic to the transported
short complex of the cone of the shifted bounded map. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
        hom
        shift ≅
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
        hom
        shift :=
  shortComplexOfDistTriangleIsoOfIso
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
      hom
      shift)
    ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
      hom).shiftedTriangle_distinguished
      shift)

/-- The short-complex comparison is induced by Mathlib's shifted mapping-cone triangle
isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
        hom
        shift =
      shortComplexOfDistTriangleIsoOfIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift)
        ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
          hom).shiftedTriangle_distinguished
          shift) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
