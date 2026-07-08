import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Projections.ExactTriangles.Owner

/-!
# Exact-calculus projection for chosen cofiber triangles

This file specializes the arbitrary distinguished-triangle exact calculus to
the chosen cofiber triangle of a morphism in the analytic stable-infinity
category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The chosen cofiber triangle of a morphism carries the stable
exact-triangle calculus without requiring downstream code to supply the
distinguishedness proof separately. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangle_exact_calculus
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
          .cofiberTriangle morphism).mor₁ ≫
        (traceAnalyticStableInfinityCategory
          .cofiberTriangle morphism).mor₂ =
          0 ∧
      (traceAnalyticStableInfinityCategory
          .cofiberTriangle morphism).mor₂ ≫
        (traceAnalyticStableInfinityCategory
          .cofiberTriangle morphism).mor₃ =
          0 ∧
        (traceAnalyticStableInfinityCategory
            .cofiberTriangle morphism).mor₃ ≫
          (traceAnalyticStableInfinityCategory
            .cofiberTriangle morphism).mor₁⟦(1 : ℤ)⟧' =
            0) ∧
      ((traceAnalyticStableInfinityCategory
        .shortComplexOfDistinguishedTriangle
          (traceAnalyticStableInfinityCategory.cofiberTriangle morphism)
          (traceAnalyticStableInfinityCategory
            .cofiberTriangle_distinguished morphism)).map
            (preadditiveCoyoneda.obj leftProbe)).Exact ∧
        ((traceAnalyticStableInfinityCategory
          .shortComplexOfDistinguishedTriangle
            (traceAnalyticStableInfinityCategory.cofiberTriangle morphism)
            (traceAnalyticStableInfinityCategory
              .cofiberTriangle_distinguished morphism)).op.map
              (preadditiveYoneda.obj rightProbe)).Exact :=
  traceAnalyticStableInfinityCategory_distinguishedTriangle_exact_calculus
    (traceAnalyticStableInfinityCategory.cofiberTriangle morphism)
    (traceAnalyticStableInfinityCategory.cofiberTriangle_distinguished
      morphism)
    leftProbe
    rightProbe

end AnalyticMotives
end LFunctions
end Boundary
