import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.Owner

/-!
# Rotation of bounded analytic distinguished triangles

The bounded package records bounded representatives for the first two vertices
of an actual distinguished triangle.  Rotating the underlying triangle preserves
distinguishedness in the analytic homotopy category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

/-- The rotated underlying triangle of a bounded distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.rotatedTriangle
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  boundedTriangle.triangle.rotate

/-- The inverse-rotated underlying triangle of a bounded distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.inverseRotatedTriangle
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  boundedTriangle.triangle.invRotate

/-- Rotating preserves the underlying distinguished triangle condition. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.rotatedTriangle_distinguished
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.rotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  rot_of_distTriang
    boundedTriangle.triangle
    boundedTriangle.distinguished

/-- Inverse rotation preserves the underlying distinguished triangle condition. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.inverseRotatedTriangle_distinguished
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.inverseRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  inv_rot_of_distTriang
    boundedTriangle.triangle
    boundedTriangle.distinguished

/-- The rotated triangle is the Mathlib rotation of the underlying triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.rotatedTriangle_eq
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.rotatedTriangle =
      boundedTriangle.triangle.rotate :=
  rfl

/-- The inverse-rotated triangle is the Mathlib inverse rotation of the underlying triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.inverseRotatedTriangle_eq
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.inverseRotatedTriangle =
      boundedTriangle.triangle.invRotate :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
