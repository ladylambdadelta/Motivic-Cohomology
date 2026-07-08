import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Subcategories.Monotonicity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Shift.Owner

/-!
# Shift transport for derived homological bound subcategories

This file lifts the concrete shift-transport formulas for analytic derived
homological bounds to functors on the corresponding full subcategories.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

attribute [local instance]
  TraceAnalyticDerivedMotiveCategory.hasDerivedCategory

/-- Shifting carries the derived homological aisle at `cut` to the aisle at
`cut - shift`. -/
abbrev HomologicalAisle.shift
    {cut : ℤ}
    (shift : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle cut ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalAisle (cut - shift) :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticDerivedMotiveCategory.HomologicalLE (cut - shift))
    (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion cut ⋙
      CategoryTheory.shiftFunctor
        TraceAnalyticDerivedMotiveCategory
        shift)
    (fun object =>
      TraceAnalyticDerivedMotiveCategory.homologicalLE_shift
        cut
        shift
        object.obj
        object.property)

/-- Shifting carries the derived homological coaisle at `cut` to the coaisle at
`cut - shift`. -/
abbrev HomologicalCoaisle.shift
    {cut : ℤ}
    (shift : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle (cut - shift) :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticDerivedMotiveCategory.HomologicalGE (cut - shift))
    (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion cut ⋙
      CategoryTheory.shiftFunctor
        TraceAnalyticDerivedMotiveCategory
        shift)
    (fun object =>
      TraceAnalyticDerivedMotiveCategory.homologicalGE_shift
        cut
        shift
        object.obj
        object.property)

/-- Shifting carries a bounded homological window to the shifted bounded
window. -/
abbrev HomologicalWindow.shift
    {lower upper : ℤ}
    (shift : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper ⥤
      TraceAnalyticDerivedMotiveCategory
        .HomologicalWindow (lower - shift) (upper - shift) :=
  CategoryTheory.FullSubcategory.lift
    (fun object : TraceAnalyticDerivedMotiveCategory =>
      TraceAnalyticDerivedMotiveCategory.HomologicalGE
          (lower - shift)
          object ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (upper - shift)
          object)
    (TraceAnalyticDerivedMotiveCategory.HomologicalWindow.inclusion
        lower
        upper ⋙
      CategoryTheory.shiftFunctor
        TraceAnalyticDerivedMotiveCategory
        shift)
    (fun object =>
      And.intro
        (TraceAnalyticDerivedMotiveCategory.homologicalGE_shift
          lower
          shift
          object.obj
          object.property.left)
        (TraceAnalyticDerivedMotiveCategory.homologicalLE_shift
          upper
          shift
          object.obj
          object.property.right))

/-- Shifting carries the diagonal heart at `cut` to the diagonal heart at
`cut - shift`. -/
abbrev HomologicalHeart.shift
    {cut : ℤ}
    (shift : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart (cut - shift) :=
  TraceAnalyticDerivedMotiveCategory.HomologicalWindow.shift
    (lower := cut)
    (upper := cut)
    shift

/-- Aisle shift commutes with the ambient derived-motive inclusion. -/
theorem HomologicalAisle.shift_comp_inclusion
    {cut : ℤ}
    (shift : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle.shift shift ⋙
        TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
          (cut - shift) =
      TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion cut ⋙
        CategoryTheory.shiftFunctor
          TraceAnalyticDerivedMotiveCategory
          shift :=
  rfl

/-- Coaisle shift commutes with the ambient derived-motive inclusion. -/
theorem HomologicalCoaisle.shift_comp_inclusion
    {cut : ℤ}
    (shift : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.shift shift ⋙
        TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
          (cut - shift) =
      TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion cut ⋙
        CategoryTheory.shiftFunctor
          TraceAnalyticDerivedMotiveCategory
          shift :=
  rfl

/-- Window shift commutes with the ambient derived-motive inclusion. -/
theorem HomologicalWindow.shift_comp_inclusion
    {lower upper : ℤ}
    (shift : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalWindow.shift shift ⋙
        TraceAnalyticDerivedMotiveCategory.HomologicalWindow.inclusion
          (lower - shift)
          (upper - shift) =
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow.inclusion
          lower
          upper ⋙
        CategoryTheory.shiftFunctor
          TraceAnalyticDerivedMotiveCategory
          shift :=
  rfl

/-- Heart shift commutes with the ambient derived-motive inclusion. -/
theorem HomologicalHeart.shift_comp_inclusion
    {cut : ℤ}
    (shift : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart.shift shift ⋙
        TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion
          (cut - shift) =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut ⋙
        CategoryTheory.shiftFunctor
          TraceAnalyticDerivedMotiveCategory
          shift :=
  rfl

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
