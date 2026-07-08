import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.NullSubcategory.Owner

/-!
# Extension closure for the stable null subcategory

This file exposes the null-subcategory closure rule in forms used by cone and
Verdier-localization arguments.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

/-- Any zero object belongs to the stable null subcategory. -/
theorem TraceAnalyticStableNullSubcategory.mem_of_isZero
    (object : TraceAnalyticAdditiveHomotopyCategory)
    (zeroObject : IsZero object) :
    TraceAnalyticStableNullSubcategory.P object :=
  CategoryTheory.mem_of_iso
    (P := TraceAnalyticStableNullSubcategory.P)
    zeroObject.isoZero.symm
    TraceAnalyticStableNullObject.zero_mem

/-- Distinguished extensions of stable-null objects are stable-null. -/
theorem TraceAnalyticStableNullSubcategory.extension_mem
    (triangle : Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (left : TraceAnalyticStableNullSubcategory.P triangle.obj₁)
    (right : TraceAnalyticStableNullSubcategory.P triangle.obj₃) :
    TraceAnalyticStableNullSubcategory.P triangle.obj₂ :=
  TraceAnalyticStableNullObject.extension_mem
    triangle
    distinguished
    left
    right

/-- If the left vertex is zero and the right vertex is stable-null, then the
middle vertex of a distinguished triangle is stable-null. -/
theorem TraceAnalyticStableNullSubcategory.extension_mem_of_isZero_left
    (triangle : Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (leftZero : IsZero triangle.obj₁)
    (right : TraceAnalyticStableNullSubcategory.P triangle.obj₃) :
    TraceAnalyticStableNullSubcategory.P triangle.obj₂ :=
  TraceAnalyticStableNullSubcategory.extension_mem
    triangle
    distinguished
    (TraceAnalyticStableNullSubcategory.mem_of_isZero
      triangle.obj₁
      leftZero)
    right

/-- If the right vertex is zero and the left vertex is stable-null, then the
middle vertex of a distinguished triangle is stable-null. -/
theorem TraceAnalyticStableNullSubcategory.extension_mem_of_isZero_right
    (triangle : Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (left : TraceAnalyticStableNullSubcategory.P triangle.obj₁)
    (rightZero : IsZero triangle.obj₃) :
    TraceAnalyticStableNullSubcategory.P triangle.obj₂ :=
  TraceAnalyticStableNullSubcategory.extension_mem
    triangle
    distinguished
    left
    (TraceAnalyticStableNullSubcategory.mem_of_isZero
      triangle.obj₃
      rightZero)

/-- If the left and right vertices are zero, then the middle vertex of a
distinguished triangle is stable-null. -/
theorem TraceAnalyticStableNullSubcategory.extension_mem_of_isZero_ends
    (triangle : Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (leftZero : IsZero triangle.obj₁)
    (rightZero : IsZero triangle.obj₃) :
    TraceAnalyticStableNullSubcategory.P triangle.obj₂ :=
  TraceAnalyticStableNullSubcategory.extension_mem
    triangle
    distinguished
    (TraceAnalyticStableNullSubcategory.mem_of_isZero
      triangle.obj₁
      leftZero)
    (TraceAnalyticStableNullSubcategory.mem_of_isZero
      triangle.obj₃
      rightZero)

/-- A distinguished triangle whose cone vertex is obtained as a stable-null
extension has an inverted first map. -/
theorem TraceAnalyticStableNullSubcategory.inverted_firstMap_of_extension_cone
    (triangle : Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (coneTriangle : Triangle TraceAnalyticAdditiveHomotopyCategory)
    (coneDistinguished :
      coneTriangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (coneVertexEq : triangle.obj₃ = coneTriangle.obj₂)
    (left : TraceAnalyticStableNullSubcategory.P coneTriangle.obj₁)
    (right : TraceAnalyticStableNullSubcategory.P coneTriangle.obj₃) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms triangle.mor₁ :=
  TraceAnalyticStableNullSubcategory.inverted_firstMap_of_triangle
    distinguished
    (Eq.subst
      (motive := fun object =>
        TraceAnalyticStableNullSubcategory.P object)
      (Eq.symm coneVertexEq)
      (TraceAnalyticStableNullSubcategory.extension_mem
        coneTriangle
        coneDistinguished
        left
        right))

end AnalyticMotives
end LFunctions
end Boundary
