import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Current.Full.Owner

/-!
# Projections from the full current stable fragment

This file exposes the three top-level components of the full current stable
package attached to one morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The full current stable package contains the exact-triangle stability
fragment. -/
theorem traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
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
  (traceAnalyticStableInfinityCategory_current_full_stability_fragment
    morphism
    leftProbe
    rightProbe).left

/-- The full current stable package contains the fiber-map/cofiber-boundary
identity. -/
theorem traceAnalyticStableInfinityCategory_current_full_fiberMap_identity
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.fiberMap morphism =
      -((traceAnalyticStableInfinityCategory
        .cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  (traceAnalyticStableInfinityCategory_current_full_stability_fragment
    morphism
    leftProbe
    rightProbe).right.left

/-- The full current stable package contains the fiber-connecting/cofiber
cocone identity. -/
theorem traceAnalyticStableInfinityCategory_current_full_connecting_identity
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    (traceAnalyticStableInfinityCategory
      .fiberTriangle morphism).mor₃ =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap
          morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  (traceAnalyticStableInfinityCategory_current_full_stability_fragment
    morphism
    leftProbe
    rightProbe).right.right

end AnalyticMotives
end LFunctions
end Boundary
