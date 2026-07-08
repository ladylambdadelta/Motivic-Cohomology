import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.Monotone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.ThirdIsoBounded.Owner

/-!
# Monotonicity of bounded triangles with iso-bounded third representatives

Increasing the numeric weight bound rebounds the first two bounded vertices and
the third representative's bounded degree data, while preserving the underlying
triangle and third representative complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rebound a bounded triangle with third iso-bounded data along a larger bound. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        lower) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
      upper where
  boundedTriangle := package.boundedTriangle.rebound bound_le
  thirdComplex := package.thirdRepresentativeComplex
  thirdObject_eq := package.thirdObject_eq
  thirdIsoBounded := package.thirdDegreewiseIsoBounded.rebound bound_le

/-- Rebounding preserves the representative third complex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.rebound_thirdRepresentativeComplex
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        lower) :
    (package.rebound bound_le).thirdRepresentativeComplex =
      package.thirdRepresentativeComplex :=
  rfl

/-- Rebounding preserves the underlying distinguished triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.rebound_triangle
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        lower) :
    (package.rebound bound_le).trianglePackage.triangle =
      package.trianglePackage.triangle :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
