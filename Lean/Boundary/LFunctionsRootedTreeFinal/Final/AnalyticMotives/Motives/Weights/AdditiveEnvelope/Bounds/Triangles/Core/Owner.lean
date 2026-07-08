import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Triangulated.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Homotopy.Owner

/-!
# Bounded distinguished triangles in the analytic homotopy category

A bounded distinguished triangle is an actual distinguished triangle in the
additive analytic homotopy category together with bounded analytic complexes
which represent its first two vertices.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A distinguished triangle whose first two vertices are represented by bounded complexes. -/
structure TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
    (bound : Nat) where
  first : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound
  second : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound
  triangle : Triangle TraceAnalyticAdditiveHomotopyCategory
  distinguished :
    triangle ∈ TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles

/-- The first homotopy-category object carried by a bounded distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.firstObject
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject
    boundedTriangle.first

/-- The second homotopy-category object carried by a bounded distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.secondObject
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject
    boundedTriangle.second

/-- The first vertex of the underlying distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.triangleFirstVertex
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    TraceAnalyticAdditiveHomotopyCategory :=
  boundedTriangle.triangle.obj₁

/-- The second vertex of the underlying distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.triangleSecondVertex
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    TraceAnalyticAdditiveHomotopyCategory :=
  boundedTriangle.triangle.obj₂

/-- The third vertex of the underlying distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.triangleThirdVertex
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    TraceAnalyticAdditiveHomotopyCategory :=
  boundedTriangle.triangle.obj₃

/-- The first morphism in the underlying distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.firstMap
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.triangle.obj₁ ⟶ boundedTriangle.triangle.obj₂ :=
  boundedTriangle.triangle.mor₁

/-- The second morphism in the underlying distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.secondMap
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.triangle.obj₂ ⟶ boundedTriangle.triangle.obj₃ :=
  boundedTriangle.triangle.mor₂

/-- The third morphism in the underlying distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.thirdMap
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.triangle.obj₃ ⟶ boundedTriangle.triangle.obj₁⟦(1 : ℤ)⟧ :=
  boundedTriangle.triangle.mor₃

/-- The bounded first representative projects to the recorded bounded object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.firstObject_eq
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject
        boundedTriangle.first :=
  rfl

/-- The bounded second representative projects to the recorded bounded object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.secondObject_eq
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject
        boundedTriangle.second :=
  rfl

/-- The underlying triangle is distinguished. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.triangle_distinguished
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  boundedTriangle.distinguished

end AnalyticMotives
end LFunctions
end Boundary
