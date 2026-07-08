import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Owner

/-!
# Subcategory vertices from chosen Yoneda truncation data

This file packages the lower and upper vertices of a chosen Yoneda truncation
triangle as objects of the concrete derived homological aisle and coaisle.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

namespace YonedaTruncationRepresentative

/-- The chosen lower truncation vertex as an object of the homological aisle. -/
def lowerAisleObject
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut) :=
  ⟨representative.lowerObject, representative.lowerObject_mem⟩

/-- The chosen upper truncation vertex as an object of the homological
coaisle. -/
def upperCoaisleObject
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut :=
  ⟨representative.upperObject, representative.upperObject_mem⟩

/-- The lower aisle object's ambient motive is the chosen lower object. -/
theorem lowerAisleObject_object
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.lowerAisleObject.object = representative.lowerObject :=
  rfl

/-- The upper coaisle object's ambient motive is the chosen upper object. -/
theorem upperCoaisleObject_object
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.upperCoaisleObject.object = representative.upperObject :=
  rfl

/-- Including the lower aisle object recovers the chosen lower object. -/
theorem lowerAisleObject_inclusion
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).obj
        representative.lowerAisleObject =
      representative.lowerObject :=
  rfl

/-- Including the upper coaisle object recovers the chosen upper object. -/
theorem upperCoaisleObject_inclusion
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion cut).obj
        representative.upperCoaisleObject =
      representative.upperObject :=
  rfl

/-- The lower aisle object carries the lower membership proof of the chosen
truncation data. -/
theorem lowerAisleObject_membership
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.lowerAisleObject.membership =
      representative.lowerObject_mem :=
  rfl

/-- The upper coaisle object carries the upper membership proof of the chosen
truncation data. -/
theorem upperCoaisleObject_membership
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.upperCoaisleObject.membership =
      representative.upperObject_mem :=
  rfl

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
