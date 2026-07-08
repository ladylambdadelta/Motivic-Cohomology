import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Transport.Owner

/-!
# The full subcategory for the concrete analytic motivic heart

This file packages the concrete cutwise heart predicate as a full subcategory
and exposes its aisle and coaisle projections.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The full subcategory of objects in the analytic motivic heart at `cut`. -/
abbrev TraceAnalyticMotivicTStructure.Heart
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticMotivicTStructure.heartAt cut)

/-- The ambient stable comparison-source object carried by a heart object. -/
def TraceAnalyticMotivicTStructure.Heart.object
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Heart cut) :
    TraceAnalyticDMgmComparisonSource :=
  object.obj

/-- The heart membership certificate carried by a heart object. -/
def TraceAnalyticMotivicTStructure.Heart.membership
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Heart cut) :
    TraceAnalyticMotivicTStructure.heartAt cut object.object :=
  object.property

/-- The inclusion of the heart at `cut` into the stable comparison source. -/
abbrev TraceAnalyticMotivicTStructure.Heart.inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart cut ⥤
      TraceAnalyticDMgmComparisonSource :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticMotivicTStructure.heartAt cut)

/-- The heart inclusion sends a heart object to its ambient object. -/
theorem TraceAnalyticMotivicTStructure.Heart.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Heart cut) :
    (TraceAnalyticMotivicTStructure.Heart.inclusion cut).obj object =
      object.object :=
  rfl

/-- A heart object determines an object of the aisle at the same cut. -/
def TraceAnalyticMotivicTStructure.Heart.toAisleObject
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Heart cut) :
    TraceAnalyticMotivicTStructure.Aisle cut :=
  ⟨
    object.object,
    TraceAnalyticMotivicTStructure.heartAt_aisle object.membership
  ⟩

/-- A heart object determines an object of the coaisle at the same cut. -/
def TraceAnalyticMotivicTStructure.Heart.toCoaisleObject
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Heart cut) :
    TraceAnalyticMotivicTStructure.Coaisle cut :=
  ⟨
    object.object,
    TraceAnalyticMotivicTStructure.heartAt_coaisle object.membership
  ⟩

/-- The heart-to-aisle object has the same ambient object. -/
theorem TraceAnalyticMotivicTStructure.Heart.toAisleObject_object
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Heart cut) :
    (TraceAnalyticMotivicTStructure.Heart.toAisleObject object).object =
      object.object :=
  rfl

/-- The heart-to-coaisle object has the same ambient object. -/
theorem TraceAnalyticMotivicTStructure.Heart.toCoaisleObject_object
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Heart cut) :
    (TraceAnalyticMotivicTStructure.Heart.toCoaisleObject object).object =
      object.object :=
  rfl

/-- The projection functor from the heart to the aisle at the same cut. -/
abbrev TraceAnalyticMotivicTStructure.Heart.toAisle
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart cut ⥤
      TraceAnalyticMotivicTStructure.Aisle cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.aisleLE cut)
    (TraceAnalyticMotivicTStructure.Heart.inclusion cut)
    (fun object =>
      TraceAnalyticMotivicTStructure.heartAt_aisle object.property)

/-- The projection functor from the heart to the coaisle at the same cut. -/
abbrev TraceAnalyticMotivicTStructure.Heart.toCoaisle
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart cut ⥤
      TraceAnalyticMotivicTStructure.Coaisle cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.coaisleGE cut)
    (TraceAnalyticMotivicTStructure.Heart.inclusion cut)
    (fun object =>
      TraceAnalyticMotivicTStructure.heartAt_coaisle object.property)

/-- The heart-to-aisle functor sends objects to the object-level aisle
projection. -/
theorem TraceAnalyticMotivicTStructure.Heart.toAisle_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Heart cut) :
    (TraceAnalyticMotivicTStructure.Heart.toAisle cut).obj object =
      TraceAnalyticMotivicTStructure.Heart.toAisleObject object :=
  rfl

/-- The heart-to-coaisle functor sends objects to the object-level coaisle
projection. -/
theorem TraceAnalyticMotivicTStructure.Heart.toCoaisle_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.Heart cut) :
    (TraceAnalyticMotivicTStructure.Heart.toCoaisle cut).obj object =
      TraceAnalyticMotivicTStructure.Heart.toCoaisleObject object :=
  rfl

/-- Heart-to-aisle followed by aisle inclusion is the heart inclusion. -/
theorem TraceAnalyticMotivicTStructure.Heart.toAisle_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart.toAisle cut ⋙
        TraceAnalyticMotivicTStructure.Aisle.inclusion cut =
      TraceAnalyticMotivicTStructure.Heart.inclusion cut :=
  rfl

/-- Heart-to-coaisle followed by coaisle inclusion is the heart inclusion. -/
theorem TraceAnalyticMotivicTStructure.Heart.toCoaisle_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.Heart.toCoaisle cut ⋙
        TraceAnalyticMotivicTStructure.Coaisle.inclusion cut =
      TraceAnalyticMotivicTStructure.Heart.inclusion cut :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
