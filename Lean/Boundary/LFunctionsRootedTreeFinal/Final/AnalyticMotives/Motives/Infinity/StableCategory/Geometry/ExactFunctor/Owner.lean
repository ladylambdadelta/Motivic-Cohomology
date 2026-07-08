import Mathlib.CategoryTheory.Triangulated.Functor
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Shift.Owner

/-!
# Exact functors on analytic stable motive triangles

This owner file records the exact functorial structure already supplied by
the analytic stable motive category itself: identity exactness and exactness
of every integer shift on distinguished triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The triangle functor induced by the identity functor on analytic stable
motives. -/
def TraceAnalyticStableMotiveQuasicategory.identityMapTriangle :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      TraceAnalyticStableMotiveQuasicategory.triangleCategory :=
  (𝟭 StableInfinityOwner.PresentedCategory).mapTriangle

/-- The identity triangle functor is canonically isomorphic to the identity
functor on the analytic triangle category. -/
def TraceAnalyticStableMotiveQuasicategory.identityMapTriangleIso :
    TraceAnalyticStableMotiveQuasicategory.identityMapTriangle ≅
      𝟭 TraceAnalyticStableMotiveQuasicategory.triangleCategory :=
  Functor.mapTriangleIdIso StableInfinityOwner.PresentedCategory

/-- The identity triangle functor preserves distinguished analytic stable
motive triangles. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.identityMapTriangle_obj_distinguished
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ TraceAnalyticStableMotiveQuasicategory
        .distinguishedTriangles) :
    TraceAnalyticStableMotiveQuasicategory
        .identityMapTriangle.obj triangle ∈
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  (𝟭 StableInfinityOwner.PresentedCategory).map_distinguished
    triangle
    distinguished

/-- The degree-shift functor on analytic stable motive triangles preserves
distinguished triangles. -/
theorem TraceAnalyticStableMotiveQuasicategory.triangleShift_obj_distinguished
    (degree : ℤ)
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ TraceAnalyticStableMotiveQuasicategory
        .distinguishedTriangles) :
    (TraceAnalyticStableMotiveQuasicategory
        .triangleShiftFunctor degree).obj triangle ∈
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  Pretriangulated.Triangle.shift_distinguished
    triangle
    distinguished
    degree

/-- The identity triangle functor is the functor induced by the identity
functor on the presented analytic stable motive category. -/
theorem TraceAnalyticStableMotiveQuasicategory.identityMapTriangle_eq :
    TraceAnalyticStableMotiveQuasicategory.identityMapTriangle =
      (𝟭 StableInfinityOwner.PresentedCategory).mapTriangle :=
  rfl

/-- The identity-triangle isomorphism is Mathlib's identity-triangle
isomorphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.identityMapTriangleIso_eq :
    TraceAnalyticStableMotiveQuasicategory.identityMapTriangleIso =
      Functor.mapTriangleIdIso StableInfinityOwner.PresentedCategory :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
