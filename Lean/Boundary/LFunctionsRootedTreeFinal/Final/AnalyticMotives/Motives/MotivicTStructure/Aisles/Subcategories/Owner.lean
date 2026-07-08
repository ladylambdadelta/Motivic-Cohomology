import Mathlib.CategoryTheory.FullSubcategory
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Shift.Owner

/-!
# Full subcategories for analytic motivic aisles and coaisles

This file packages the concrete aisle and coaisle predicates as full
subcategories of the stable analytic comparison source.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The full subcategory of objects in the analytic motivic aisle at `cut`. -/
abbrev TraceAnalyticMotivicTStructure.Aisle
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticMotivicTStructure.aisleLE cut)

/-- The full subcategory of objects in the analytic motivic coaisle at `cut`. -/
abbrev TraceAnalyticMotivicTStructure.Coaisle
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticMotivicTStructure.coaisleGE cut)

/-- The ambient stable comparison-source object carried by an aisle object. -/
def TraceAnalyticMotivicTStructure.Aisle.object
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Aisle cut) :
    TraceAnalyticDMgmComparisonSource :=
  object.obj

/-- The ambient stable comparison-source object carried by a coaisle object. -/
def TraceAnalyticMotivicTStructure.Coaisle.object
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Coaisle cut) :
    TraceAnalyticDMgmComparisonSource :=
  object.obj

/-- The aisle membership certificate carried by an aisle object. -/
def TraceAnalyticMotivicTStructure.Aisle.membership
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Aisle cut) :
    TraceAnalyticMotivicTStructure.aisleLE cut object.object :=
  object.property

/-- The coaisle membership certificate carried by a coaisle object. -/
def TraceAnalyticMotivicTStructure.Coaisle.membership
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Coaisle cut) :
    TraceAnalyticMotivicTStructure.coaisleGE cut object.object :=
  object.property

/-- The inclusion of the aisle at `cut` into the stable comparison source. -/
abbrev TraceAnalyticMotivicTStructure.Aisle.inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Aisle cut ⥤
      TraceAnalyticDMgmComparisonSource :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticMotivicTStructure.aisleLE cut)

/-- The inclusion of the coaisle at `cut` into the stable comparison source. -/
abbrev TraceAnalyticMotivicTStructure.Coaisle.inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Coaisle cut ⥤
      TraceAnalyticDMgmComparisonSource :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticMotivicTStructure.coaisleGE cut)

/-- The aisle inclusion sends an aisle object to its ambient object. -/
theorem TraceAnalyticMotivicTStructure.Aisle.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Aisle cut) :
    (TraceAnalyticMotivicTStructure.Aisle.inclusion cut).obj object =
      object.object :=
  rfl

/-- The coaisle inclusion sends a coaisle object to its ambient object. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Coaisle cut) :
    (TraceAnalyticMotivicTStructure.Coaisle.inclusion cut).obj object =
      object.object :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
