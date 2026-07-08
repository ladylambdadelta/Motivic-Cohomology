import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Bicartesian.Owner

/-!
# Current stable exact-triangle fragments

This file packages the currently proved stability data for one morphism in
the analytic stable motive presentation: cofiber and fiber distinguished
triangles, the inverse-rotation relation between them, zero-compositions, and
covariant plus contravariant preadditive Yoneda exactness for the associated
short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The currently proved exact-triangle stability fragment attached to one
morphism in the analytic stable motive presentation. -/
theorem traceAnalyticStableInfinityCategory_current_stability_fragment
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    (traceAnalyticStableInfinityCategory.cofiberTriangle morphism ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
      traceAnalyticStableInfinityCategory.fiberTriangle morphism ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
        traceAnalyticStableInfinityCategory.fiberTriangle morphism =
          (traceAnalyticStableInfinityCategory
            .cofiberTriangle morphism).invRotate) ∧
      traceAnalyticStableInfinityCategory.fiberObject morphism =
        (traceAnalyticStableInfinityCategory
          .cofiberObject morphism)⟦(-1 : ℤ)⟧ ∧
        (morphism ≫
              traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism =
            0 ∧
          traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism ≫
              traceAnalyticStableInfinityCategory.cofiberBoundary morphism =
            0 ∧
            traceAnalyticStableInfinityCategory.cofiberBoundary morphism ≫
                morphism⟦(1 : ℤ)⟧' =
              0 ∧
              traceAnalyticStableInfinityCategory.fiberMap morphism ≫
                  morphism =
                0) ∧
          (((traceAnalyticStableInfinityCategory
            .cofiberShortComplex morphism).map
              (preadditiveCoyoneda.obj leftProbe)).Exact ∧
            ((traceAnalyticStableInfinityCategory
              .fiberShortComplex morphism).map
                (preadditiveCoyoneda.obj leftProbe)).Exact) ∧
            (((traceAnalyticStableInfinityCategory
              .cofiberShortComplex morphism).op.map
                (preadditiveYoneda.obj rightProbe)).Exact ∧
              ((traceAnalyticStableInfinityCategory
                .fiberShortComplex morphism).op.map
                  (preadditiveYoneda.obj rightProbe)).Exact) :=
  And.intro
    (traceAnalyticStableInfinityCategory_cofiberFiberTriangle_stability
      morphism)
    (And.intro
      (traceAnalyticStableInfinityCategory_fiberObject_is_desuspended_cofiber
        morphism)
      (And.intro
        (traceAnalyticStableInfinityCategory_cofiberFiber_zero_compositions
          morphism)
        (And.intro
          (traceAnalyticStableInfinityCategory_cofiberFiber_coyoneda_exact
            morphism
            leftProbe)
          (traceAnalyticStableInfinityCategory_cofiberFiber_yoneda_exact
            morphism
            rightProbe))))

end AnalyticMotives
end LFunctions
end Boundary
