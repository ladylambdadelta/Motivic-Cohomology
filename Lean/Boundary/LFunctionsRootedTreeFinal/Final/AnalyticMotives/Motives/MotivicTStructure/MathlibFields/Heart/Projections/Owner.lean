import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Heart.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.IsoClosure.Subcategories.Owner

/-!
# Projections from the iso-closed analytic motivic heart

This file exposes the inclusion and aisle/coaisle projection functors for the
iso-closed cutwise analytic motivic heart.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The inclusion of the iso-closed heart at `cut` into the stable comparison
source. -/
abbrev TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed cut ⥤
      TraceAnalyticDMgmComparisonSource :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticMotivicTStructure.heartAtIsoClosed cut)

/-- The iso-closed heart inclusion sends an object to its ambient object. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion cut).obj object =
      object.object :=
  rfl

/-- An iso-closed heart object determines an object of the iso-closed aisle at
the same cut. -/
def TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisleObject
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    TraceAnalyticMotivicTStructure.AisleIsoClosed cut :=
  ⟨
    object.object,
    TraceAnalyticMotivicTStructure.heartAtIsoClosed_aisle
      object.membership
  ⟩

/-- An iso-closed heart object determines an object of the iso-closed coaisle
at the same cut. -/
def TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisleObject
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    TraceAnalyticMotivicTStructure.CoaisleIsoClosed cut :=
  ⟨
    object.object,
    TraceAnalyticMotivicTStructure.heartAtIsoClosed_coaisle
      object.membership
  ⟩

/-- The iso-closed heart-to-aisle object has the same ambient object. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisleObject_object
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisleObject object).object =
      object.object :=
  rfl

/-- The iso-closed heart-to-coaisle object has the same ambient object. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisleObject_object
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisleObject object).object =
      object.object :=
  rfl

/-- The projection functor from the iso-closed heart to the iso-closed aisle at
the same cut. -/
abbrev TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisle
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed cut ⥤
      TraceAnalyticMotivicTStructure.AisleIsoClosed cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.aisleLEIsoClosed cut)
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion cut)
    (fun object =>
      TraceAnalyticMotivicTStructure.heartAtIsoClosed_aisle object.property)

/-- The projection functor from the iso-closed heart to the iso-closed coaisle
at the same cut. -/
abbrev TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisle
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed cut ⥤
      TraceAnalyticMotivicTStructure.CoaisleIsoClosed cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.coaisleGEIsoClosed cut)
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion cut)
    (fun object =>
      TraceAnalyticMotivicTStructure.heartAtIsoClosed_coaisle object.property)

/-- The iso-closed heart-to-aisle functor sends objects to the object-level
projection. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisle_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisle cut).obj object =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisleObject object :=
  rfl

/-- The iso-closed heart-to-coaisle functor sends objects to the object-level
projection. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisle_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisle cut).obj object =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisleObject object :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
