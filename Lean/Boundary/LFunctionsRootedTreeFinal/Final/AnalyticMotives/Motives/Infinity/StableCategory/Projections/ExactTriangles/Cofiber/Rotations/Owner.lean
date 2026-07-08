import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Projections.ExactTriangles.Owner

/-!
# Exact-calculus projections for rotated cofiber triangles

This file specializes the arbitrary distinguished-triangle exact calculus to
the rotated and inverse-rotated chosen cofiber triangles of a morphism in the
analytic stable-infinity category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The rotated chosen cofiber triangle of a morphism carries the stable
exact-triangle calculus without requiring downstream code to supply the
distinguishedness proof separately. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangle_exact_calculus
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
          .rotatedCofiberTriangle morphism).mor₁ ≫
        (traceAnalyticStableInfinityCategory
          .rotatedCofiberTriangle morphism).mor₂ =
          0 ∧
      (traceAnalyticStableInfinityCategory
          .rotatedCofiberTriangle morphism).mor₂ ≫
        (traceAnalyticStableInfinityCategory
          .rotatedCofiberTriangle morphism).mor₃ =
          0 ∧
        (traceAnalyticStableInfinityCategory
            .rotatedCofiberTriangle morphism).mor₃ ≫
          (traceAnalyticStableInfinityCategory
            .rotatedCofiberTriangle morphism).mor₁⟦(1 : ℤ)⟧' =
            0) ∧
      ((traceAnalyticStableInfinityCategory
        .shortComplexOfDistinguishedTriangle
          (traceAnalyticStableInfinityCategory
            .rotatedCofiberTriangle morphism)
          (traceAnalyticStableInfinityCategory
            .rotatedCofiberTriangle_distinguished morphism)).map
            (preadditiveCoyoneda.obj leftProbe)).Exact ∧
        ((traceAnalyticStableInfinityCategory
          .shortComplexOfDistinguishedTriangle
            (traceAnalyticStableInfinityCategory
              .rotatedCofiberTriangle morphism)
            (traceAnalyticStableInfinityCategory
              .rotatedCofiberTriangle_distinguished morphism)).op.map
              (preadditiveYoneda.obj rightProbe)).Exact :=
  traceAnalyticStableInfinityCategory_distinguishedTriangle_exact_calculus
    (traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism)
    (traceAnalyticStableInfinityCategory.rotatedCofiberTriangle_distinguished
      morphism)
    leftProbe
    rightProbe

/-- The inverse-rotated chosen cofiber triangle of a morphism carries the
stable exact-triangle calculus without requiring downstream code to supply
the distinguishedness proof separately. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangle_exact_calculus
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
          .invRotatedCofiberTriangle morphism).mor₁ ≫
        (traceAnalyticStableInfinityCategory
          .invRotatedCofiberTriangle morphism).mor₂ =
          0 ∧
      (traceAnalyticStableInfinityCategory
          .invRotatedCofiberTriangle morphism).mor₂ ≫
        (traceAnalyticStableInfinityCategory
          .invRotatedCofiberTriangle morphism).mor₃ =
          0 ∧
        (traceAnalyticStableInfinityCategory
            .invRotatedCofiberTriangle morphism).mor₃ ≫
          (traceAnalyticStableInfinityCategory
            .invRotatedCofiberTriangle morphism).mor₁⟦(1 : ℤ)⟧' =
            0) ∧
      ((traceAnalyticStableInfinityCategory
        .shortComplexOfDistinguishedTriangle
          (traceAnalyticStableInfinityCategory
            .invRotatedCofiberTriangle morphism)
          (traceAnalyticStableInfinityCategory
            .invRotatedCofiberTriangle_distinguished morphism)).map
            (preadditiveCoyoneda.obj leftProbe)).Exact ∧
        ((traceAnalyticStableInfinityCategory
          .shortComplexOfDistinguishedTriangle
            (traceAnalyticStableInfinityCategory
              .invRotatedCofiberTriangle morphism)
            (traceAnalyticStableInfinityCategory
              .invRotatedCofiberTriangle_distinguished morphism)).op.map
              (preadditiveYoneda.obj rightProbe)).Exact :=
  traceAnalyticStableInfinityCategory_distinguishedTriangle_exact_calculus
    (traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle morphism)
    (traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle_distinguished
      morphism)
    leftProbe
    rightProbe

end AnalyticMotives
end LFunctions
end Boundary
