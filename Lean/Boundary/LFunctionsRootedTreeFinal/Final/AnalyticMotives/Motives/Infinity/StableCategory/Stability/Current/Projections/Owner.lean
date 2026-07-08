import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Current.Owner

/-!
# Projections from current stable exact-triangle fragments

This file exposes the individual fields contained in the current per-morphism
stable exact-triangle fragment.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The current fragment gives cofiber/fiber distinguishedness and inverse
rotation for a morphism. -/
theorem traceAnalyticStableInfinityCategory_current_triangle_stability
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
      traceAnalyticStableInfinityCategory.fiberTriangle morphism ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
        traceAnalyticStableInfinityCategory.fiberTriangle morphism =
          (traceAnalyticStableInfinityCategory
            .cofiberTriangle morphism).invRotate :=
  (traceAnalyticStableInfinityCategory_current_stability_fragment
    morphism
    leftProbe
    rightProbe).left

/-- The current fragment gives the fiber-object desuspension identity. -/
theorem traceAnalyticStableInfinityCategory_current_fiberObject_desuspension
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.fiberObject morphism =
      (traceAnalyticStableInfinityCategory
        .cofiberObject morphism)⟦(-1 : ℤ)⟧ :=
  (traceAnalyticStableInfinityCategory_current_stability_fragment
    morphism
    leftProbe
    rightProbe).right.left

/-- The current fragment gives the cofiber/fiber zero-composition laws. -/
theorem traceAnalyticStableInfinityCategory_current_zero_compositions
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    morphism ≫
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
            0 :=
  (traceAnalyticStableInfinityCategory_current_stability_fragment
    morphism
    leftProbe
    rightProbe).right.right.left

/-- The current fragment gives covariant preadditive Yoneda exactness for the
cofiber and fiber short complexes. -/
theorem traceAnalyticStableInfinityCategory_current_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
      ((traceAnalyticStableInfinityCategory
        .fiberShortComplex morphism).map
          (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_current_stability_fragment
    morphism
    leftProbe
    rightProbe).right.right.right.left

/-- The current fragment gives contravariant preadditive Yoneda exactness for
the cofiber and fiber short complexes. -/
theorem traceAnalyticStableInfinityCategory_current_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact ∧
      ((traceAnalyticStableInfinityCategory
        .fiberShortComplex morphism).op.map
          (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_current_stability_fragment
    morphism
    leftProbe
    rightProbe).right.right.right.right

end AnalyticMotives
end LFunctions
end Boundary
