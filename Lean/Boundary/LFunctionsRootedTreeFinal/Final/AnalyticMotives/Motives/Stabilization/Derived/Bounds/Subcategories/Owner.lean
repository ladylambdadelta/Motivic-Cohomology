import Mathlib.CategoryTheory.FullSubcategory
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Monotonicity.Owner

/-!
# Full subcategories for derived analytic homological bounds

This file packages the concrete derived homology-vanishing predicates as full
subcategories: the nonpositive aisle, the nonnegative coaisle, bounded
windows, and the diagonal heart.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The full subcategory of derived analytic motives homologically `≤ cut`. -/
abbrev HomologicalAisle
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticDerivedMotiveCategory.HomologicalLE cut)

/-- The full subcategory of derived analytic motives homologically `≥ cut`. -/
abbrev HomologicalCoaisle
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticDerivedMotiveCategory.HomologicalGE cut)

/-- The full subcategory of derived analytic motives homologically between
`lower` and `upper`. -/
abbrev HomologicalWindow
    (lower upper : ℤ) :=
  CategoryTheory.FullSubcategory
    (fun object : TraceAnalyticDerivedMotiveCategory =>
      TraceAnalyticDerivedMotiveCategory.HomologicalGE lower object ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalLE upper object)

/-- The diagonal derived analytic heart at `cut`. -/
abbrev HomologicalHeart
    (cut : ℤ) :=
  TraceAnalyticDerivedMotiveCategory.HomologicalWindow cut cut

/-- The ambient derived motive carried by an aisle object. -/
def HomologicalAisle.object
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalAisle cut) :
    TraceAnalyticDerivedMotiveCategory :=
  object.obj

/-- The ambient derived motive carried by a coaisle object. -/
def HomologicalCoaisle.object
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut) :
    TraceAnalyticDerivedMotiveCategory :=
  object.obj

/-- The ambient derived motive carried by a bounded-window object. -/
def HomologicalWindow.object
    {lower upper : ℤ}
    (object :
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper) :
    TraceAnalyticDerivedMotiveCategory :=
  object.obj

/-- The ambient derived motive carried by a heart object. -/
def HomologicalHeart.object
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    TraceAnalyticDerivedMotiveCategory :=
  object.obj

/-- The homological `≤ cut` certificate carried by an aisle object. -/
def HomologicalAisle.membership
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalAisle cut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE cut object.object :=
  object.property

/-- The homological `≥ cut` certificate carried by a coaisle object. -/
def HomologicalCoaisle.membership
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE cut object.object :=
  object.property

/-- The homological `≥ lower` certificate carried by a bounded-window object. -/
def HomologicalWindow.lowerMembership
    {lower upper : ℤ}
    (object :
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE lower object.object :=
  object.property.left

/-- The homological `≤ upper` certificate carried by a bounded-window object. -/
def HomologicalWindow.upperMembership
    {lower upper : ℤ}
    (object :
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE upper object.object :=
  object.property.right

/-- The homological `≥ cut` certificate carried by a heart object. -/
def HomologicalHeart.lowerMembership
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE cut object.object :=
  TraceAnalyticDerivedMotiveCategory.HomologicalWindow.lowerMembership object

/-- The homological `≤ cut` certificate carried by a heart object. -/
def HomologicalHeart.upperMembership
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE cut object.object :=
  TraceAnalyticDerivedMotiveCategory.HomologicalWindow.upperMembership object

/-- The inclusion of the derived homological aisle into derived analytic
motives. -/
abbrev HomologicalAisle.inclusion
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle cut ⥤
      TraceAnalyticDerivedMotiveCategory :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticDerivedMotiveCategory.HomologicalLE cut)

/-- The inclusion of the derived homological coaisle into derived analytic
motives. -/
abbrev HomologicalCoaisle.inclusion
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut ⥤
      TraceAnalyticDerivedMotiveCategory :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticDerivedMotiveCategory.HomologicalGE cut)

/-- The inclusion of a derived homological window into derived analytic
motives. -/
abbrev HomologicalWindow.inclusion
    (lower upper : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper ⥤
      TraceAnalyticDerivedMotiveCategory :=
  CategoryTheory.fullSubcategoryInclusion
    (fun object : TraceAnalyticDerivedMotiveCategory =>
      TraceAnalyticDerivedMotiveCategory.HomologicalGE lower object ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalLE upper object)

/-- The inclusion of a derived homological heart into derived analytic
motives. -/
abbrev HomologicalHeart.inclusion
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ⥤
      TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticDerivedMotiveCategory.HomologicalWindow.inclusion cut cut

/-- The aisle inclusion sends an object to its ambient derived motive. -/
theorem HomologicalAisle.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalAisle cut) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion cut).obj
        object =
      object.object :=
  rfl

/-- The coaisle inclusion sends an object to its ambient derived motive. -/
theorem HomologicalCoaisle.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion cut).obj
        object =
      object.object :=
  rfl

/-- A bounded-window object determines an object of the coaisle at its lower
cut. -/
def HomologicalWindow.toCoaisleObject
    {lower upper : ℤ}
    (object :
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle lower :=
  ⟨object.object, object.lowerMembership⟩

/-- A bounded-window object determines an object of the aisle at its upper
cut. -/
def HomologicalWindow.toAisleObject
    {lower upper : ℤ}
    (object :
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle upper :=
  ⟨object.object, object.upperMembership⟩

/-- The projection functor from a window to its lower coaisle. -/
abbrev HomologicalWindow.toCoaisle
    (lower upper : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle lower :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticDerivedMotiveCategory.HomologicalGE lower)
    (TraceAnalyticDerivedMotiveCategory.HomologicalWindow.inclusion
      lower
      upper)
    (fun object => object.property.left)

/-- The projection functor from a window to its upper aisle. -/
abbrev HomologicalWindow.toAisle
    (lower upper : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalAisle upper :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticDerivedMotiveCategory.HomologicalLE upper)
    (TraceAnalyticDerivedMotiveCategory.HomologicalWindow.inclusion
      lower
      upper)
    (fun object => object.property.right)

/-- The window-to-coaisle projection sends objects to the object-level
projection. -/
theorem HomologicalWindow.toCoaisle_obj
    {lower upper : ℤ}
    (object :
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalWindow.toCoaisle
        lower
        upper).obj object =
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow.toCoaisleObject
        object :=
  rfl

/-- The window-to-aisle projection sends objects to the object-level
projection. -/
theorem HomologicalWindow.toAisle_obj
    {lower upper : ℤ}
    (object :
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow lower upper) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalWindow.toAisle
        lower
        upper).obj object =
      TraceAnalyticDerivedMotiveCategory.HomologicalWindow.toAisleObject
        object :=
  rfl

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
