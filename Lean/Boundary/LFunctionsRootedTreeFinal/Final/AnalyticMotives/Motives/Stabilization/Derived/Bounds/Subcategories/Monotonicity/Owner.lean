import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Subcategories.Owner

/-!
# Monotone transport between derived homological bound subcategories

This file turns the predicate-level monotonicity of derived homological bounds
into concrete functors between the corresponding full subcategories.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Increasing the cut gives an inclusion of derived homological aisles. -/
abbrev HomologicalAisle.liftCut
    {sourceCut targetCut : ℤ}
    (hcut : sourceCut ≤ targetCut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle sourceCut ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalAisle targetCut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticDerivedMotiveCategory.HomologicalLE targetCut)
    (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
      sourceCut)
    (fun object =>
      TraceAnalyticDerivedMotiveCategory.homologicalLE_mono
        hcut
        object.obj
        object.property)

/-- Decreasing the cut gives an inclusion of derived homological coaisles. -/
abbrev HomologicalCoaisle.lowerCut
    {targetCut sourceCut : ℤ}
    (hcut : targetCut ≤ sourceCut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle sourceCut ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle targetCut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticDerivedMotiveCategory.HomologicalGE targetCut)
    (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
      sourceCut)
    (fun object =>
      TraceAnalyticDerivedMotiveCategory.homologicalGE_antitone
        hcut
        object.obj
        object.property)

/-- Widening a homological window gives an inclusion of full subcategories. -/
abbrev HomologicalWindow.widen
    {sourceLower targetLower sourceUpper targetUpper : ℤ}
    (hlower : targetLower ≤ sourceLower)
    (hupper : sourceUpper ≤ targetUpper) :
    TraceAnalyticDerivedMotiveCategory
        .HomologicalWindow sourceLower sourceUpper ⥤
      TraceAnalyticDerivedMotiveCategory
        .HomologicalWindow targetLower targetUpper :=
  CategoryTheory.FullSubcategory.lift
    (fun object : TraceAnalyticDerivedMotiveCategory =>
      TraceAnalyticDerivedMotiveCategory.HomologicalGE targetLower object ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalLE targetUpper object)
    (TraceAnalyticDerivedMotiveCategory.HomologicalWindow.inclusion
      sourceLower
      sourceUpper)
    (fun object =>
      And.symm
        (TraceAnalyticDerivedMotiveCategory.homological_window_mono
          hlower
          hupper
          object.obj
          object.property.right
          object.property.left))

/-- The monotone aisle transport commutes with the ambient inclusion. -/
theorem HomologicalAisle.liftCut_comp_inclusion
    {sourceCut targetCut : ℤ}
    (hcut : sourceCut ≤ targetCut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle.liftCut hcut ⋙
        TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
          targetCut =
      TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
        sourceCut :=
  rfl

/-- The monotone coaisle transport commutes with the ambient inclusion. -/
theorem HomologicalCoaisle.lowerCut_comp_inclusion
    {targetCut sourceCut : ℤ}
    (hcut : targetCut ≤ sourceCut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.lowerCut hcut ⋙
        TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
          targetCut =
      TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
        sourceCut :=
  rfl

/-- The window-widening functor commutes with the ambient inclusion. -/
theorem HomologicalWindow.widen_comp_inclusion
    {sourceLower targetLower sourceUpper targetUpper : ℤ}
    (hlower : targetLower ≤ sourceLower)
    (hupper : sourceUpper ≤ targetUpper) :
    TraceAnalyticDerivedMotiveCategory.HomologicalWindow.widen
          hlower
          hupper ⋙
        TraceAnalyticDerivedMotiveCategory.HomologicalWindow.inclusion
          targetLower
          targetUpper =
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow.inclusion
        sourceLower
        sourceUpper :=
  rfl

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
