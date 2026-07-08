import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Subcategories.Owner

/-!
# Heart projections to aisle and coaisle subcategories

This file exposes the diagonal homological heart as a simultaneous object of
the corresponding coaisle and aisle at the same cut.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- A heart object determines an object of the coaisle at the same cut. -/
def HomologicalHeart.toCoaisleObject
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut :=
  TraceAnalyticDerivedMotiveCategory.HomologicalWindow.toCoaisleObject object

/-- A heart object determines an object of the aisle at the same cut. -/
def HomologicalHeart.toAisleObject
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle cut :=
  TraceAnalyticDerivedMotiveCategory.HomologicalWindow.toAisleObject object

/-- The projection functor from the heart to the coaisle at the same cut. -/
abbrev HomologicalHeart.toCoaisle
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut :=
  TraceAnalyticDerivedMotiveCategory.HomologicalWindow.toCoaisle cut cut

/-- The projection functor from the heart to the aisle at the same cut. -/
abbrev HomologicalHeart.toAisle
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalAisle cut :=
  TraceAnalyticDerivedMotiveCategory.HomologicalWindow.toAisle cut cut

/-- The heart-to-coaisle projection sends objects to the object-level
projection. -/
theorem HomologicalHeart.toCoaisle_obj
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toCoaisle cut).obj
        object =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toCoaisleObject
        object :=
  rfl

/-- The heart-to-aisle projection sends objects to the object-level
projection. -/
theorem HomologicalHeart.toAisle_obj
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toAisle cut).obj
        object =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toAisleObject
        object :=
  rfl

/-- Projecting a heart object to the coaisle and then including it recovers
the heart object's ambient derived motive. -/
theorem HomologicalHeart.toCoaisle_inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion cut).obj
        (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toCoaisleObject
          object) =
      object.object :=
  rfl

/-- Projecting a heart object to the aisle and then including it recovers the
heart object's ambient derived motive. -/
theorem HomologicalHeart.toAisle_inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion cut).obj
        (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toAisleObject
          object) =
      object.object :=
  rfl

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
