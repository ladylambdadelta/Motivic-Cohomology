import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.Owner

/-!
# Bounded triangles with degreewise iso-bounded third representatives

This package refines a bounded distinguished triangle by adding a concrete
complex representing the third vertex whose degree objects are bounded up to
analytic isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A bounded triangle together with degreewise iso-bounded data for its third vertex. -/
structure TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
    (bound : Nat) where
  boundedTriangle :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound
  thirdComplex : TraceAnalyticAdditiveCochainComplex
  thirdObject_eq :
    boundedTriangle.triangleThirdVertex =
      TraceAnalyticAdditiveHomotopyCategory.objectOf thirdComplex
  thirdIsoBounded :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
      thirdComplex
      bound

/-- The underlying bounded distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.trianglePackage
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound :=
  package.boundedTriangle

/-- The concrete complex representing the third vertex. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.thirdRepresentativeComplex
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    TraceAnalyticAdditiveCochainComplex :=
  package.thirdComplex

/-- The third vertex is the homotopy image of the recorded representative complex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.thirdObject_eq_objectOf
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    package.boundedTriangle.triangleThirdVertex =
      TraceAnalyticAdditiveHomotopyCategory.objectOf
        package.thirdRepresentativeComplex :=
  package.thirdObject_eq

/-- The representative complex is degreewise iso-bounded by the same bound. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.thirdDegreewiseIsoBounded
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound) :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
      package.thirdRepresentativeComplex
      bound :=
  package.thirdIsoBounded

end AnalyticMotives
end LFunctions
end Boundary
