import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Projections.Global.Owner

/-!
# Current full-stability projections from the actual stable-infinity certificate

This file exposes the three components of the current full-stability fragment
as direct consequences of the actual analytic stable-infinity structure
certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The actual stable-infinity certificate supplies the exact-triangle
stability fragment in the current full package. -/
theorem traceAnalyticStableInfinityCategory_actual_global_current_full_exactTriangle_fragment
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
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
  (traceAnalyticStableInfinityCategory_actual_global_current_full_stability
    morphism
    leftProbe
    rightProbe).left

/-- The actual stable-infinity certificate supplies the current full
fiber-map/cofiber-boundary identity. -/
theorem traceAnalyticStableInfinityCategory_actual_global_current_full_fiberMap_identity
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.fiberMap morphism =
      -((traceAnalyticStableInfinityCategory
        .cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  (traceAnalyticStableInfinityCategory_actual_global_current_full_stability
    morphism
    leftProbe
    rightProbe).right.left

/-- The actual stable-infinity certificate supplies the current full
fiber-connecting/cofiber-cocone identity. -/
theorem traceAnalyticStableInfinityCategory_actual_global_current_full_connecting_identity
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    (traceAnalyticStableInfinityCategory
      .fiberTriangle morphism).mor₃ =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap
          morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  (traceAnalyticStableInfinityCategory_actual_global_current_full_stability
    morphism
    leftProbe
    rightProbe).right.right

end AnalyticMotives
end LFunctions
end Boundary
