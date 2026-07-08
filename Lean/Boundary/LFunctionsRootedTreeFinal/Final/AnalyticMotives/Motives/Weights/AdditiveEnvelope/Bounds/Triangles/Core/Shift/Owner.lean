import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.Owner

/-!
# Shifts of bounded distinguished triangles

Bounded distinguished triangles are stable under the Mathlib triangle shift.
The bounded representatives for the first two vertices are the concrete
cochain shifts of the original bounded complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The shifted underlying triangle of a bounded distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.shiftedTriangle
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound)
    (shift : ℤ) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  (CategoryTheory.shiftFunctor
      (Triangle TraceAnalyticAdditiveHomotopyCategory)
      shift).obj
    boundedTriangle.triangle

/-- The shifted underlying triangle is distinguished. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.shiftedTriangle_distinguished
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound)
    (shift : ℤ) :
    boundedTriangle.shiftedTriangle shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  Triangle.shift_distinguished
    boundedTriangle.triangle
    boundedTriangle.triangle_distinguished
    shift

/-- Shift a bounded distinguished triangle by shifting its triangle and first two representatives. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.shift
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound where
  first := boundedTriangle.first.shift shift
  second := boundedTriangle.second.shift shift
  triangle := boundedTriangle.shiftedTriangle shift
  distinguished := boundedTriangle.shiftedTriangle_distinguished shift

/-- The shifted bounded triangle has the shifted first bounded representative. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.shift_first
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound)
    (shift : ℤ) :
    (boundedTriangle.shift shift).first =
      boundedTriangle.first.shift shift :=
  rfl

/-- The shifted bounded triangle has the shifted second bounded representative. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.shift_second
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound)
    (shift : ℤ) :
    (boundedTriangle.shift shift).second =
      boundedTriangle.second.shift shift :=
  rfl

/-- The shifted bounded triangle has the shifted underlying triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.shift_triangle
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound)
    (shift : ℤ) :
    (boundedTriangle.shift shift).triangle =
      boundedTriangle.shiftedTriangle shift :=
  rfl

/-- The first shifted-triangle vertex is the shifted first vertex of the original triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.shiftedTriangle_obj₁
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound)
    (shift : ℤ) :
    (boundedTriangle.shiftedTriangle shift).obj₁ =
      boundedTriangle.triangle.obj₁⟦shift⟧ :=
  rfl

/-- The second shifted-triangle vertex is the shifted second vertex of the original triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.shiftedTriangle_obj₂
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound)
    (shift : ℤ) :
    (boundedTriangle.shiftedTriangle shift).obj₂ =
      boundedTriangle.triangle.obj₂⟦shift⟧ :=
  rfl

/-- The third shifted-triangle vertex is the shifted third vertex of the original triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.shiftedTriangle_obj₃
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound)
    (shift : ℤ) :
    (boundedTriangle.shiftedTriangle shift).obj₃ =
      boundedTriangle.triangle.obj₃⟦shift⟧ :=
  rfl

/-- The shifted bounded triangle is distinguished. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.shift_distinguished
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound)
    (shift : ℤ) :
    (boundedTriangle.shift shift).triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  (boundedTriangle.shift shift).triangle_distinguished

end AnalyticMotives
end LFunctions
end Boundary
