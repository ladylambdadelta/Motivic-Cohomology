import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Projections.ExactTriangles.Owner

/-!
# Exact-calculus projection for chosen fiber triangles

This file specializes the arbitrary distinguished-triangle exact calculus to
the chosen fiber triangle of a morphism in the analytic stable-infinity
category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The chosen fiber triangle of a morphism carries the stable
exact-triangle calculus without requiring downstream code to supply the
distinguishedness proof separately. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangle_exact_calculus
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
          .fiberTriangle morphism).mor₁ ≫
        (traceAnalyticStableInfinityCategory
          .fiberTriangle morphism).mor₂ =
          0 ∧
      (traceAnalyticStableInfinityCategory
          .fiberTriangle morphism).mor₂ ≫
        (traceAnalyticStableInfinityCategory
          .fiberTriangle morphism).mor₃ =
          0 ∧
        (traceAnalyticStableInfinityCategory
            .fiberTriangle morphism).mor₃ ≫
          (traceAnalyticStableInfinityCategory
            .fiberTriangle morphism).mor₁⟦(1 : ℤ)⟧' =
            0) ∧
      ((traceAnalyticStableInfinityCategory
        .shortComplexOfDistinguishedTriangle
          (traceAnalyticStableInfinityCategory.fiberTriangle morphism)
          (traceAnalyticStableInfinityCategory
            .fiberTriangle_distinguished morphism)).map
            (preadditiveCoyoneda.obj leftProbe)).Exact ∧
        ((traceAnalyticStableInfinityCategory
          .shortComplexOfDistinguishedTriangle
            (traceAnalyticStableInfinityCategory.fiberTriangle morphism)
            (traceAnalyticStableInfinityCategory
              .fiberTriangle_distinguished morphism)).op.map
              (preadditiveYoneda.obj rightProbe)).Exact :=
  traceAnalyticStableInfinityCategory_distinguishedTriangle_exact_calculus
    (traceAnalyticStableInfinityCategory.fiberTriangle morphism)
    (traceAnalyticStableInfinityCategory.fiberTriangle_distinguished
      morphism)
    leftProbe
    rightProbe

end AnalyticMotives
end LFunctions
end Boundary
