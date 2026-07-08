import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Transport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Owner

/-!
# Full subcategories for analytic motivic windows

This file packages interval windows as full subcategories of the stable
analytic comparison source and exposes their aisle/coaisle projections.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The full subcategory of objects in the analytic motivic window
`[lower, upper]`. -/
abbrev TraceAnalyticMotivicTStructure.Window
    (lower upper : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticMotivicTStructure.window lower upper)

/-- The ambient stable comparison-source object carried by a window object. -/
def TraceAnalyticMotivicTStructure.Window.object
    {lower upper : ℤ}
    (object : TraceAnalyticMotivicTStructure.Window lower upper) :
    TraceAnalyticDMgmComparisonSource :=
  object.obj

/-- The window membership certificate carried by a window object. -/
def TraceAnalyticMotivicTStructure.Window.membership
    {lower upper : ℤ}
    (object : TraceAnalyticMotivicTStructure.Window lower upper) :
    TraceAnalyticMotivicTStructure.window lower upper object.object :=
  object.property

/-- The inclusion of a window into the stable comparison source. -/
abbrev TraceAnalyticMotivicTStructure.Window.inclusion
    (lower upper : ℤ) :
    TraceAnalyticMotivicTStructure.Window lower upper ⥤
      TraceAnalyticDMgmComparisonSource :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticMotivicTStructure.window lower upper)

/-- The window inclusion sends a window object to its ambient object. -/
theorem TraceAnalyticMotivicTStructure.Window.inclusion_obj
    {lower upper : ℤ}
    (object : TraceAnalyticMotivicTStructure.Window lower upper) :
    (TraceAnalyticMotivicTStructure.Window.inclusion lower upper).obj object =
      object.object :=
  rfl

/-- A window object determines an object of the lower coaisle. -/
def TraceAnalyticMotivicTStructure.Window.toCoaisleObject
    {lower upper : ℤ}
    (object : TraceAnalyticMotivicTStructure.Window lower upper) :
    TraceAnalyticMotivicTStructure.Coaisle lower :=
  ⟨
    object.object,
    TraceAnalyticMotivicTStructure.window_coaisle object.membership
  ⟩

/-- A window object determines an object of the upper aisle. -/
def TraceAnalyticMotivicTStructure.Window.toAisleObject
    {lower upper : ℤ}
    (object : TraceAnalyticMotivicTStructure.Window lower upper) :
    TraceAnalyticMotivicTStructure.Aisle upper :=
  ⟨
    object.object,
    TraceAnalyticMotivicTStructure.window_aisle object.membership
  ⟩

/-- The projection functor from a window to its lower coaisle. -/
abbrev TraceAnalyticMotivicTStructure.Window.toCoaisle
    (lower upper : ℤ) :
    TraceAnalyticMotivicTStructure.Window lower upper ⥤
      TraceAnalyticMotivicTStructure.Coaisle lower :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.coaisleGE lower)
    (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
    (fun object =>
      TraceAnalyticMotivicTStructure.window_coaisle object.property)

/-- The projection functor from a window to its upper aisle. -/
abbrev TraceAnalyticMotivicTStructure.Window.toAisle
    (lower upper : ℤ) :
    TraceAnalyticMotivicTStructure.Window lower upper ⥤
      TraceAnalyticMotivicTStructure.Aisle upper :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.aisleLE upper)
    (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
    (fun object =>
      TraceAnalyticMotivicTStructure.window_aisle object.property)

/-- Window-to-coaisle followed by coaisle inclusion is the window inclusion. -/
theorem TraceAnalyticMotivicTStructure.Window.toCoaisle_comp_inclusion
    (lower upper : ℤ) :
    TraceAnalyticMotivicTStructure.Window.toCoaisle lower upper ⋙
        TraceAnalyticMotivicTStructure.Coaisle.inclusion lower =
      TraceAnalyticMotivicTStructure.Window.inclusion lower upper :=
  rfl

/-- Window-to-aisle followed by aisle inclusion is the window inclusion. -/
theorem TraceAnalyticMotivicTStructure.Window.toAisle_comp_inclusion
    (lower upper : ℤ) :
    TraceAnalyticMotivicTStructure.Window.toAisle lower upper ⋙
        TraceAnalyticMotivicTStructure.Aisle.inclusion upper =
      TraceAnalyticMotivicTStructure.Window.inclusion lower upper :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
