import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.Owner

/-!
# Chosen truncation triangle for represented truncation objects

This file exposes the chosen normalized truncation maps and triangle attached
to an object of the represented truncation subcategory.
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

/-- The chosen lower truncation map for a represented truncation object. -/
def firstMap
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.representative.lowerObject ⟶ object.object :=
  object.representative.firstMap

/-- The chosen upper truncation map for a represented truncation object. -/
def secondMap
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.object ⟶ object.representative.upperObject :=
  object.representative.secondMap

/-- The chosen connecting map for a represented truncation object. -/
def connectingMap
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.representative.upperObject ⟶
      object.representative.lowerObject⟦(1 : ℤ)⟧ :=
  object.representative.connectingMap

/-- The chosen truncation triangle for a represented truncation object. -/
def triangle
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    Triangle TraceAnalyticDerivedMotiveCategory :=
  object.representative.triangle

/-- The first vertex of the represented-object chosen triangle is the chosen
lower object. -/
theorem triangle_obj₁
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.triangle.obj₁ = object.representative.lowerObject :=
  object.representative.triangle_obj₁

/-- The middle vertex of the represented-object chosen triangle is the
ambient represented object. -/
theorem triangle_obj₂
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.triangle.obj₂ = object.object :=
  object.representative.triangle_obj₂

/-- The third vertex of the represented-object chosen triangle is the chosen
upper object. -/
theorem triangle_obj₃
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.triangle.obj₃ = object.representative.upperObject :=
  object.representative.triangle_obj₃

/-- The represented-object chosen triangle is distinguished. -/
theorem triangle_distinguished
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.triangle ∈ distTriang TraceAnalyticDerivedMotiveCategory :=
  object.representative.triangle_distinguished

/-- The first two maps of the represented-object chosen triangle compose to
zero. -/
theorem firstMap_comp_secondMap
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.firstMap ≫ object.secondMap = 0 :=
  object.representative.firstMap_comp_secondMap

/-- The upper map followed by the connecting map is zero. -/
theorem secondMap_comp_connectingMap
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.secondMap ≫ object.connectingMap = 0 :=
  object.representative.secondMap_comp_connectingMap

/-- The connecting map followed by the shifted lower map is zero. -/
theorem connectingMap_comp_shift_firstMap
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.connectingMap ≫ object.firstMap⟦(1 : ℤ)⟧' = 0 :=
  object.representative.connectingMap_comp_shift_firstMap

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
