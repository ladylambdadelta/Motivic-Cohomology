import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.ShortComplex.Comparison.Owner

/-!
# Components of the shifted short-complex comparison

The short-complex isomorphism induced by the shifted mapping-cone triangle
isomorphism has vertex components given by the corresponding triangle-vertex
components.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The left vertex component of the shifted short-complex comparison. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_π₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    ShortComplex.π₁.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
          hom
          shift) =
      Triangle.π₁.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift) :=
  rfl

/-- The middle vertex component of the shifted short-complex comparison. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_π₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    ShortComplex.π₂.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
          hom
          shift) =
      Triangle.π₂.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift) :=
  rfl

/-- The right vertex component of the shifted short-complex comparison. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_π₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    ShortComplex.π₃.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
          hom
          shift) =
      Triangle.π₃.mapIso
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedTriangleIsoShiftedMap
          hom
          shift) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
