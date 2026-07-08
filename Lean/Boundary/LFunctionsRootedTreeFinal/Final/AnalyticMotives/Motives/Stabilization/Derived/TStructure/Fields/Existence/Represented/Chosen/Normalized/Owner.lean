import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Subcategories.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Projections.Owner

/-!
# Normalized chosen Yoneda truncation data

This file specializes the chosen Yoneda truncation data to the adjacent
`≤ 0`, `≥ 1` t-structure shape.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

namespace YonedaTruncationRepresentative

/-- The normalized lower aisle object for a cut-`1` Yoneda representative. -/
def lowerAisleObjectZero
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle 0 :=
  ⟨representative.lowerObject, representative.lowerObject_mem⟩

/-- The normalized upper coaisle object for a cut-`1` Yoneda representative. -/
def upperCoaisleObjectOne
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle 1 :=
  representative.upperCoaisleObject

/-- Including the normalized lower aisle object recovers the chosen lower
object. -/
theorem lowerAisleObjectZero_inclusion
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion 0).obj
        representative.lowerAisleObjectZero =
      representative.lowerObject :=
  rfl

/-- Including the normalized upper coaisle object recovers the chosen upper
object. -/
theorem upperCoaisleObjectOne_inclusion
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion 1).obj
        representative.upperCoaisleObjectOne =
      representative.upperObject :=
  rfl

/-- The normalized lower aisle object's ambient motive is the chosen lower
object. -/
theorem lowerAisleObjectZero_object
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    representative.lowerAisleObjectZero.object = representative.lowerObject :=
  rfl

/-- The normalized upper coaisle object's ambient motive is the chosen upper
object. -/
theorem upperCoaisleObjectOne_object
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    representative.upperCoaisleObjectOne.object = representative.upperObject :=
  rfl

/-- The normalized chosen truncation triangle has the chosen lower object as
its first vertex. -/
theorem normalized_triangle_obj₁
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    representative.triangle.obj₁ = representative.lowerObject :=
  representative.triangle_obj₁

/-- The normalized chosen truncation triangle has the represented object as
its middle vertex. -/
theorem normalized_triangle_obj₂
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    representative.triangle.obj₂ = object :=
  representative.triangle_obj₂

/-- The normalized chosen truncation triangle has the chosen upper object as
its third vertex. -/
theorem normalized_triangle_obj₃
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    representative.triangle.obj₃ = representative.upperObject :=
  representative.triangle_obj₃

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
