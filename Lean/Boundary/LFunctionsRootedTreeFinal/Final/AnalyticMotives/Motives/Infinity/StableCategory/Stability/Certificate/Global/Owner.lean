import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Current.Full.Owner

/-!
# Global stability certificate for analytic stable motives

This file bundles the proved stability behavior of the concrete analytic
stable-infinity owner object into one proposition-level certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The concrete analytic stable-infinity owner object carries the global
stable behavior used downstream: every morphism has compatible cofiber and
fiber triangles, distinguished triangles have zero-composition and Yoneda
exactness, rotation and completion hold, and the current per-morphism
fiber/cofiber stability fragment is available uniformly. -/
theorem traceAnalyticStableInfinityCategory_global_stability_certificate :
    (∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      traceAnalyticStableInfinityCategory_cofiberTriangleFor morphism ∈
          traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
        traceAnalyticStableInfinityCategory_fiberTriangleFor morphism ∈
          traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
          traceAnalyticStableInfinityCategory_fiberTriangleFor morphism =
            (traceAnalyticStableInfinityCategory_cofiberTriangleFor
              morphism).invRotate) ∧
      (∀ (triangle : StableInfinityOwner.PresentedTriangle)
        (distinguished :
          triangle ∈
            traceAnalyticStableInfinityCategory.distinguishedTriangles),
        triangle.mor₁ ≫ triangle.mor₂ = 0 ∧
          triangle.mor₂ ≫ triangle.mor₃ = 0 ∧
            triangle.mor₃ ≫ triangle.mor₁⟦(1 : ℤ)⟧' = 0) ∧
        (∀ (triangle : StableInfinityOwner.PresentedTriangle)
          (distinguished :
            triangle ∈
              traceAnalyticStableInfinityCategory.distinguishedTriangles)
          (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
          (rightProbe : StableInfinityOwner.PresentedCategory),
          ((traceAnalyticStableInfinityCategory
            .shortComplexOfDistinguishedTriangle
              triangle
              distinguished).map
              (preadditiveCoyoneda.obj leftProbe)).Exact ∧
            ((traceAnalyticStableInfinityCategory
              .shortComplexOfDistinguishedTriangle
                triangle
                distinguished).op.map
                (preadditiveYoneda.obj rightProbe)).Exact) ∧
          (∀ {source target : StableInfinityOwner.PresentedCategory}
            (morphism : source ⟶ target)
            (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
            (rightProbe : StableInfinityOwner.PresentedCategory),
            traceAnalyticStableInfinityCategory_current_full_stability_fragment
              morphism
              leftProbe
              rightProbe) ∧
            (∀ object : StableInfinityOwner.PresentedCategory,
              Pretriangulated.contractibleTriangle object ∈
                traceAnalyticStableInfinityCategory.distinguishedTriangles) ∧
              (∀ triangle : StableInfinityOwner.PresentedTriangle,
                triangle ∈
                    traceAnalyticStableInfinityCategory.distinguishedTriangles ↔
                  triangle.rotate ∈
                    traceAnalyticStableInfinityCategory
                      .distinguishedTriangles) :=
  And.intro
    (fun morphism =>
      And.intro
        (traceAnalyticStableInfinityCategory_cofiberTriangleFor_distinguished
          morphism)
        (And.intro
          (traceAnalyticStableInfinityCategory_fiberTriangleFor_distinguished
            morphism)
          (traceAnalyticStableInfinityCategory_fiberTriangleFor_eq_invRotate
            morphism)))
    (And.intro
      (fun triangle distinguished =>
        And.intro
          (traceAnalyticStableInfinityCategory_distinguished_mor₁_comp_mor₂
            triangle
            distinguished)
          (And.intro
            (traceAnalyticStableInfinityCategory_distinguished_mor₂_comp_mor₃
              triangle
              distinguished)
            (traceAnalyticStableInfinityCategory_distinguished_mor₃_comp_shift_mor₁
              triangle
              distinguished)))
      (And.intro
        (fun triangle distinguished leftProbe rightProbe =>
          And.intro
            (traceAnalyticStableInfinityCategory_distinguished_coyoneda_exact
              triangle
              distinguished
              leftProbe)
            (traceAnalyticStableInfinityCategory_distinguished_yoneda_exact
              triangle
              distinguished
              rightProbe))
        (And.intro
          (fun morphism leftProbe rightProbe =>
            traceAnalyticStableInfinityCategory_current_full_stability_fragment
              morphism
              leftProbe
              rightProbe)
          (And.intro
            traceAnalyticStableInfinityCategory_contractibleTriangle_distinguished
            traceAnalyticStableInfinityCategory_rotate_distinguishedTriangle))))

end AnalyticMotives
end LFunctions
end Boundary
