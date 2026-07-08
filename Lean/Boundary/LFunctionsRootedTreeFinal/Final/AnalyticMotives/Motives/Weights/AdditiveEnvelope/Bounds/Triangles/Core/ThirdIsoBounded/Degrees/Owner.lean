import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.ThirdIsoBounded.Owner

/-!
# Degree accessors for third iso-bounded triangle packages

This file exposes the actual degree object of the third representative complex,
its bounded representative, and the isomorphism between them.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The actual degree object of the third representative complex. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.thirdDegreeObject
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject :=
  package.thirdRepresentativeComplex.objectAt degree

/-- The iso-bounded datum attached to a third-representative degree. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.thirdDegreeIsoBounded
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject.IsoBoundedBy
      (package.thirdDegreeObject degree)
      bound :=
  package.thirdDegreewiseIsoBounded.degreeObject degree

/-- The bounded representative of a third-representative degree. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.thirdDegreeBoundedRepresentative
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject.BoundedBy bound :=
  (package.thirdDegreeIsoBounded degree).boundedRepresentative

/-- The actual third-degree object is isomorphic to its bounded representative. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.thirdDegreeIsoRepresentative
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound)
    (degree : ℤ) :
    package.thirdDegreeObject degree ≅
      (package.thirdDegreeBoundedRepresentative degree).object :=
  (package.thirdDegreeIsoBounded degree).objectIsoRepresentative

/-- The third-degree bounded representative satisfies the ambient bound. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded.thirdDegreeBoundedRepresentative_weightLevel_le
    {bound : Nat}
    (package :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
        bound)
    (degree : ℤ) :
    (package.thirdDegreeBoundedRepresentative degree).object.weightLevel ≤
      bound :=
  (package.thirdDegreeIsoBounded degree).representative_weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
