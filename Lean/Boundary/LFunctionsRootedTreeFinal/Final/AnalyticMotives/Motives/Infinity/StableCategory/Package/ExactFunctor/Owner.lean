import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.ExactFunctor.Owner

/-!
# Package-level exact triangle functors

This owner file exposes identity and shift exactness for analytic stable
triangles through the assembled stable-infinity package surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level identity triangle functor is the functor induced by the
identity functor on the presented analytic stable motive category. -/
theorem traceAnalyticStableInfinityCategory_identityMapTriangle_eq :
    traceAnalyticStableInfinityCategory.identityMapTriangle =
      (𝟭 StableInfinityOwner.PresentedCategory).mapTriangle :=
  rfl

/-- The package-level identity-triangle isomorphism is Mathlib's
identity-triangle isomorphism. -/
theorem traceAnalyticStableInfinityCategory_identityMapTriangleIso_eq :
    traceAnalyticStableInfinityCategory.identityMapTriangleIso =
      Functor.mapTriangleIdIso StableInfinityOwner.PresentedCategory :=
  rfl

/-- The package-level identity triangle functor preserves distinguished
analytic stable triangles. -/
theorem
    traceAnalyticStableInfinityCategory_identityMapTriangle_obj_distinguished
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    traceAnalyticStableInfinityCategory.identityMapTriangle.obj
        triangle ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .identityMapTriangle_obj_distinguished triangle distinguished

/-- Package-level triangle shifts preserve distinguished analytic stable
triangles. -/
theorem traceAnalyticStableInfinityCategory_triangleShift_obj_distinguished
    (degree : ℤ)
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    (traceAnalyticStableInfinityCategory
      .triangleShiftFunctor degree).obj triangle ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .triangleShift_obj_distinguished degree triangle distinguished

end AnalyticMotives
end LFunctions
end Boundary
