import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Heart.Owner

/-!
# Projections from the support heart

This file exposes the inclusion and support-aisle/support-coaisle projection
functors for the support heart.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The full subcategory of support `LE` objects at `cut`. -/
abbrev SupportAisle
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE cut)

/-- The full subcategory of support `GE` objects at `cut`. -/
abbrev SupportCoaisle
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE cut)

/-- The degreewise bounded stable object carried by a support-aisle object. -/
def SupportAisle.object
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportAisle cut) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  object.obj

/-- The degreewise bounded stable object carried by a support-coaisle object. -/
def SupportCoaisle.object
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportCoaisle cut) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  object.obj

/-- The support-aisle inclusion into the degreewise bounded stable source. -/
abbrev SupportAisle.inclusion
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportAisle cut ⥤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE cut)

/-- The support-coaisle inclusion into the degreewise bounded stable source. -/
abbrev SupportCoaisle.inclusion
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportCoaisle cut ⥤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE cut)

/-- The support-aisle inclusion sends an object to its carried object. -/
theorem SupportAisle.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportAisle cut) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportAisle.inclusion cut).obj object =
      object.object :=
  rfl

/-- The support-coaisle inclusion sends an object to its carried object. -/
theorem SupportCoaisle.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportCoaisle cut) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportCoaisle.inclusion cut).obj object =
      object.object :=
  rfl

/-- The inclusion of the support heart into the degreewise bounded stable
source. -/
abbrev SupportHeart.inclusion
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportHeart cut ⥤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart cut)

/-- The support-heart inclusion sends an object to its carried object. -/
theorem SupportHeart.inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart.inclusion cut).obj object =
      object.object :=
  rfl

/-- A support-heart object determines a support-aisle object at the same cut. -/
def SupportHeart.toAisleObject
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportAisle cut :=
  ⟨
    object.object,
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart_aisle object.membership
  ⟩

/-- A support-heart object determines a support-coaisle object at the same cut. -/
def SupportHeart.toCoaisleObject
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportCoaisle cut :=
  ⟨
    object.object,
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart_coaisle object.membership
  ⟩

/-- The support-heart-to-aisle object has the same carried object. -/
theorem SupportHeart.toAisleObject_object
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart.toAisleObject object).object =
      object.object :=
  rfl

/-- The support-heart-to-coaisle object has the same carried object. -/
theorem SupportHeart.toCoaisleObject_object
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart.toCoaisleObject object).object =
      object.object :=
  rfl

/-- The projection functor from the support heart to the support aisle. -/
abbrev SupportHeart.toAisle
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportHeart cut ⥤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportAisle cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE cut)
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart.inclusion cut)
    (fun object =>
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportHeart_aisle object.property)

/-- The projection functor from the support heart to the support coaisle. -/
abbrev SupportHeart.toCoaisle
    (cut : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportHeart cut ⥤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportCoaisle cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE cut)
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart.inclusion cut)
    (fun object =>
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportHeart_coaisle object.property)

/-- The support-heart-to-aisle functor sends objects to the object-level
projection. -/
theorem SupportHeart.toAisle_obj
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart.toAisle cut).obj object =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportHeart.toAisleObject object :=
  rfl

/-- The support-heart-to-coaisle functor sends objects to the object-level
projection. -/
theorem SupportHeart.toCoaisle_obj
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart.toCoaisle cut).obj object =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .SupportHeart.toCoaisleObject object :=
  rfl

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
