import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Owner

/-!
# Contractible triangles in the analytic stable motive category

This owner file exposes the contractible-triangle functor attached to the
analytic stable motive category and records that its values are distinguished
triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The functor sending an analytic stable motive to its contractible
triangle. -/
def TraceAnalyticStableMotiveQuasicategory.contractibleTriangleFunctor :
    StableInfinityOwner.PresentedCategory ⥤
      TraceAnalyticStableMotiveQuasicategory.triangleCategory :=
  Pretriangulated.contractibleTriangleFunctor
    StableInfinityOwner.PresentedCategory

/-- The contractible-triangle functor is Mathlib's contractible-triangle
functor. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.contractibleTriangleFunctor_eq :
    TraceAnalyticStableMotiveQuasicategory.contractibleTriangleFunctor =
      Pretriangulated.contractibleTriangleFunctor
        StableInfinityOwner.PresentedCategory :=
  rfl

/-- The contractible triangle of an analytic stable motive is distinguished. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.contractibleTriangleFunctor_obj_distinguished
    (object : StableInfinityOwner.PresentedCategory) :
    (TraceAnalyticStableMotiveQuasicategory.contractibleTriangleFunctor.obj
        object) ∈
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  TraceAnalyticStableMotiveQuasicategory
    .contractibleTriangle_distinguished
    object

end AnalyticMotives
end LFunctions
end Boundary
