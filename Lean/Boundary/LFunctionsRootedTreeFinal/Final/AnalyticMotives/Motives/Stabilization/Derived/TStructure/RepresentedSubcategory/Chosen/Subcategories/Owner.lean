import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.ShortComplex.Owner

/-!
# Aisle and coaisle vertices for represented truncation objects

This file exposes the normalized lower and upper truncation vertices of a
represented truncation object as concrete objects of the homological aisle and
coaisle subcategories.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

namespace RepresentedTruncationObject

/-- Including the represented object's normalized lower aisle object recovers
the chosen lower truncation object. -/
theorem lowerAisleObjectZero_inclusion
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion 0).obj
        object.lowerAisleObjectZero =
      object.representative.lowerObject :=
  object.representative.lowerAisleObjectZero_inclusion

/-- Including the represented object's normalized upper coaisle object
recovers the chosen upper truncation object. -/
theorem upperCoaisleObjectOne_inclusion
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion 1).obj
        object.upperCoaisleObjectOne =
      object.representative.upperObject :=
  object.representative.upperCoaisleObjectOne_inclusion

/-- The ambient object of the represented object's normalized lower aisle
object is the chosen lower truncation object. -/
theorem lowerAisleObjectZero_object
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.lowerAisleObjectZero.object =
      object.representative.lowerObject :=
  object.representative.lowerAisleObjectZero_object

/-- The ambient object of the represented object's normalized upper coaisle
object is the chosen upper truncation object. -/
theorem upperCoaisleObjectOne_object
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.upperCoaisleObjectOne.object =
      object.representative.upperObject :=
  object.representative.upperCoaisleObjectOne_object

/-- The represented object's chosen short complex starts at the included
normalized lower aisle object. -/
theorem shortComplex_X₁_inclusion
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.shortComplex.X₁ =
      (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion 0).obj
        object.lowerAisleObjectZero :=
  object.representative.normalized_shortComplex_X₁_inclusion

/-- The represented object's chosen short complex ends at the included
normalized upper coaisle object. -/
theorem shortComplex_X₃_inclusion
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.shortComplex.X₃ =
      (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion 1).obj
        object.upperCoaisleObjectOne :=
  object.representative.normalized_shortComplex_X₃_inclusion

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
