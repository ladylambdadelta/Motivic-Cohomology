import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.IsoClosure.Representatives.Owner

/-!
# Full subcategories for iso-closed analytic motivic aisles and coaisles

This file packages the Mathlib-ready iso-closed analytic aisle and coaisle
predicates as full subcategories of the stable comparison source.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The full subcategory of objects in the iso-closed analytic motivic aisle at
`cut`. -/
abbrev TraceAnalyticMotivicTStructure.AisleIsoClosed
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticMotivicTStructure.aisleLEIsoClosed cut)

/-- The full subcategory of objects in the iso-closed analytic motivic coaisle
at `cut`. -/
abbrev TraceAnalyticMotivicTStructure.CoaisleIsoClosed
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticMotivicTStructure.coaisleGEIsoClosed cut)

/-- The ambient stable comparison-source object carried by an iso-closed aisle
object. -/
def TraceAnalyticMotivicTStructure.AisleIsoClosed.object
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.AisleIsoClosed cut) :
    TraceAnalyticDMgmComparisonSource :=
  object.obj

/-- The ambient stable comparison-source object carried by an iso-closed
coaisle object. -/
def TraceAnalyticMotivicTStructure.CoaisleIsoClosed.object
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.CoaisleIsoClosed cut) :
    TraceAnalyticDMgmComparisonSource :=
  object.obj

/-- The iso-closed aisle membership certificate carried by an iso-closed aisle
object. -/
def TraceAnalyticMotivicTStructure.AisleIsoClosed.membership
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.AisleIsoClosed cut) :
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed cut object.object :=
  object.property

/-- The iso-closed coaisle membership certificate carried by an iso-closed
coaisle object. -/
def TraceAnalyticMotivicTStructure.CoaisleIsoClosed.membership
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.CoaisleIsoClosed cut) :
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed cut object.object :=
  object.property

/-- The inclusion of the iso-closed aisle at `cut` into the stable comparison
source. -/
abbrev TraceAnalyticMotivicTStructure.AisleIsoClosed.inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.AisleIsoClosed cut ⥤
      TraceAnalyticDMgmComparisonSource :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticMotivicTStructure.aisleLEIsoClosed cut)

/-- The inclusion of the iso-closed coaisle at `cut` into the stable comparison
source. -/
abbrev TraceAnalyticMotivicTStructure.CoaisleIsoClosed.inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.CoaisleIsoClosed cut ⥤
      TraceAnalyticDMgmComparisonSource :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticMotivicTStructure.coaisleGEIsoClosed cut)

/-- The iso-closed aisle inclusion sends an object to its ambient object. -/
theorem TraceAnalyticMotivicTStructure.AisleIsoClosed.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.AisleIsoClosed cut) :
    (TraceAnalyticMotivicTStructure.AisleIsoClosed.inclusion cut).obj object =
      object.object :=
  rfl

/-- The iso-closed coaisle inclusion sends an object to its ambient object. -/
theorem TraceAnalyticMotivicTStructure.CoaisleIsoClosed.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.CoaisleIsoClosed cut) :
    (TraceAnalyticMotivicTStructure.CoaisleIsoClosed.inclusion cut).obj object =
      object.object :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
