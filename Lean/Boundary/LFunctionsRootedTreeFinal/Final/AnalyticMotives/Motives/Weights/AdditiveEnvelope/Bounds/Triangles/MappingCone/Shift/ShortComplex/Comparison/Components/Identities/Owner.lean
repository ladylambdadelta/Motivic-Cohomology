import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.ShortComplex.Comparison.Components.Hom.Commutativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.ShortComplex.Comparison.Components.Inv.Commutativity.Owner

/-!
# Component inverse identities for the shifted short-complex comparison

The forward and inverse component maps of the shifted short-complex comparison
compose to identity maps on each vertex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left forward component followed by the left inverse component is identity. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₁_comp_inv₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₁
          hom
          shift ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₁
          hom
          shift =
      𝟙 (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
        hom
        shift).X₁ :=
  congrArg
    ShortComplex.Hom.τ₁
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
      hom
      shift).hom_inv_id

/-- The middle forward component followed by the middle inverse component is identity. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₂_comp_inv₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₂
          hom
          shift ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₂
          hom
          shift =
      𝟙 (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
        hom
        shift).X₂ :=
  congrArg
    ShortComplex.Hom.τ₂
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
      hom
      shift).hom_inv_id

/-- The right forward component followed by the right inverse component is identity. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₃_comp_inv₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₃
          hom
          shift ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₃
          hom
          shift =
      𝟙 (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplex
        hom
        shift).X₃ :=
  congrArg
    ShortComplex.Hom.τ₃
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
      hom
      shift).hom_inv_id

/-- The left inverse component followed by the left forward component is identity. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₁_comp_hom₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₁
          hom
          shift ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₁
          hom
          shift =
      𝟙 (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
        hom
        shift).X₁ :=
  congrArg
    ShortComplex.Hom.τ₁
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
      hom
      shift).inv_hom_id

/-- The middle inverse component followed by the middle forward component is identity. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₂_comp_hom₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₂
          hom
          shift ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₂
          hom
          shift =
      𝟙 (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
        hom
        shift).X₂ :=
  congrArg
    ShortComplex.Hom.τ₂
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
      hom
      shift).inv_hom_id

/-- The right inverse component followed by the right forward component is identity. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₃_comp_hom₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_inv₃
          hom
          shift ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap_hom₃
          hom
          shift =
      𝟙 (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedMapShortComplexTransported
        hom
        shift).X₃ :=
  congrArg
    ShortComplex.Hom.τ₃
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedOriginalShortComplexIsoShiftedMap
      hom
      shift).inv_hom_id

end AnalyticMotives
end LFunctions
end Boundary
