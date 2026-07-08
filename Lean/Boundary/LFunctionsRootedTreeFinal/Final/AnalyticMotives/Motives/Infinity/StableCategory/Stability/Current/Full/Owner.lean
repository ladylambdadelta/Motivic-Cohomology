import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Current.Projections.Maps.Owner

/-!
# Full current stable fragment

This file combines the current exact-triangle stability fragment with the
map-level fiber/cofiber duality fields for one morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The full currently proved stable package attached to one morphism:
exact-triangle stability, zero-compositions, Yoneda exactness, and the two
map-level fiber/cofiber identities. -/
theorem traceAnalyticStableInfinityCategory_current_full_stability_fragment
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory.cofiberTriangle morphism ∈
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
                  (preadditiveYoneda.obj rightProbe)).Exact)) ∧
      traceAnalyticStableInfinityCategory.fiberMap morphism =
        -((traceAnalyticStableInfinityCategory
          .cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
          (shiftEquiv StableInfinityOwner.PresentedCategory
            (1 : ℤ)).unitIso.inv.app _ ∧
        (traceAnalyticStableInfinityCategory
          .fiberTriangle morphism).mor₃ =
          traceAnalyticStableInfinityCategory.cofiberCoconeMap
              morphism ≫
            (shiftEquiv StableInfinityOwner.PresentedCategory
              (1 : ℤ)).counitIso.inv.app _ :=
  And.intro
    (traceAnalyticStableInfinityCategory_current_stability_fragment
      morphism
      leftProbe
      rightProbe)
    (And.intro
      (traceAnalyticStableInfinityCategory_current_fiberMap_desuspended_boundary
        morphism)
      (traceAnalyticStableInfinityCategory_current_fiberConnectingMap_cofiberCocone
        morphism))

end AnalyticMotives
end LFunctions
end Boundary
