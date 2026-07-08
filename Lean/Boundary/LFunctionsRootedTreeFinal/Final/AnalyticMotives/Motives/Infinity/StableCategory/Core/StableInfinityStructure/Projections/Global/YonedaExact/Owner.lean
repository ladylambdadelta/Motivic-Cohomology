import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Projections.Global.Owner

/-!
# Yoneda-exactness projections from the actual global stability certificate

This file peels paired Yoneda exactness for distinguished triangles out of
the actual stable-infinity global-stability certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The short complex attached to a distinguished triangle is exact after
contravariant preadditive Yoneda evaluation. -/
theorem traceAnalyticStableInfinityCategory_actual_global_coyoneda_exact
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .shortComplexOfDistinguishedTriangle
        triangle
        distinguished).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  (traceAnalyticStableInfinityCategory_actual_global_yoneda_exact
    triangle
    distinguished
    probe
    triangle.obj₂).left

/-- The opposite short complex attached to a distinguished triangle is exact
after covariant preadditive Yoneda evaluation. -/
theorem traceAnalyticStableInfinityCategory_actual_global_yoneda_exact_right
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .shortComplexOfDistinguishedTriangle
        triangle
        distinguished).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  (traceAnalyticStableInfinityCategory_actual_global_yoneda_exact
    triangle
    distinguished
    (Opposite.op triangle.obj₂)
    probe).right

end AnalyticMotives
end LFunctions
end Boundary
