import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.ShortComplex.Comparison.Components.Owner

/-!
# Morphism components of the shifted short-complex comparison

The hom part of the shifted short-complex comparison is a morphism of short
complexes.  This file exposes its three component maps and the two commuting
squares.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left morphism component of the shifted short-complex comparison. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
      hom
      shift).X₁ ⟶
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
        hom
        shift).X₁ :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
    hom
    shift).hom.τ₁

/-- The middle morphism component of the shifted short-complex comparison. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
      hom
      shift).X₂ ⟶
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
        hom
        shift).X₂ :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
    hom
    shift).hom.τ₂

/-- The right morphism component of the shifted short-complex comparison. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
      hom
      shift).X₃ ⟶
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
        hom
        shift).X₃ :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
    hom
    shift).hom.τ₃

/-- The left component is the first component of the comparison isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₁_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₁
        hom
        shift =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
        hom
        shift).hom.τ₁ :=
  rfl

/-- The middle component is the second component of the comparison isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₂_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₂
        hom
        shift =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
        hom
        shift).hom.τ₂ :=
  rfl

/-- The right component is the third component of the comparison isomorphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₃_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₃
        hom
        shift =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
        hom
        shift).hom.τ₃ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
