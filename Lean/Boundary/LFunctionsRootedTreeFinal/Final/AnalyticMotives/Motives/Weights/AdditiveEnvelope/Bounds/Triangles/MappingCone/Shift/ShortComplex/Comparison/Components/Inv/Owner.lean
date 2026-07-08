import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.ShortComplex.Comparison.Components.Owner

/-!
# Inverse morphism components of the shifted short-complex comparison

The inverse of the shifted short-complex comparison is also a morphism of short
complexes.  This file exposes its three component maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left inverse component of the shifted short-complex comparison. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
      hom
      shift).X₁ ⟶
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
        hom
        shift).X₁ :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
    hom
    shift).inv.τ₁

/-- The middle inverse component of the shifted short-complex comparison. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
      hom
      shift).X₂ ⟶
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
        hom
        shift).X₂ :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
    hom
    shift).inv.τ₂

/-- The right inverse component of the shifted short-complex comparison. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
      hom
      shift).X₃ ⟶
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
        hom
        shift).X₃ :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
    hom
    shift).inv.τ₃

/-- The left inverse component is the first component of the inverse comparison. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₁_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₁
        hom
        shift =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
        hom
        shift).inv.τ₁ :=
  rfl

/-- The middle inverse component is the second component of the inverse comparison. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₂_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₂
        hom
        shift =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
        hom
        shift).inv.τ₂ :=
  rfl

/-- The right inverse component is the third component of the inverse comparison. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₃_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₃
        hom
        shift =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
        hom
        shift).inv.τ₃ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
