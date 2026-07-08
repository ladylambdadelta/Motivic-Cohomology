import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.ThirdIsoBounded.Owner

/-!
# Rotation of triangles with third iso-bounded representatives

The full package carries an underlying bounded distinguished triangle.  Rotating
or inverse-rotating that underlying triangle preserves distinguishedness.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The rotated underlying triangle of a package with third iso-bounded data. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.rotatedTriangle
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  package.trianglePackage.rotatedTriangle

/-- The inverse-rotated underlying triangle of a package with third iso-bounded data. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.inverseRotatedTriangle
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  package.trianglePackage.inverseRotatedTriangle

/-- Rotating preserves distinguishedness of the underlying triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.rotatedTriangle_distinguished
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.rotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  package.trianglePackage.rotatedTriangle_distinguished

/-- Inverse rotation preserves distinguishedness of the underlying triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.inverseRotatedTriangle_distinguished
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.inverseRotatedTriangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  package.trianglePackage.inverseRotatedTriangle_distinguished

end AnalyticMotives
end LFunctions
end Boundary
