import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Exact-triangle projections for the analytic stable infinity category

This file packages the exactness content of an arbitrary distinguished
triangle in the assembled analytic stable-infinity category: the three
successive zero compositions and the two preadditive Yoneda exactness tests.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A distinguished triangle in the analytic stable-infinity category carries
the usual stable exact-triangle calculus: three zero-composition laws and
covariant plus contravariant preadditive Yoneda exactness. -/
theorem traceAnalyticStableInfinityCategory_distinguishedTriangle_exact_calculus
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    (triangle.mor₁ ≫ triangle.mor₂ = 0 ∧
      triangle.mor₂ ≫ triangle.mor₃ = 0 ∧
        triangle.mor₃ ≫ triangle.mor₁⟦(1 : ℤ)⟧' = 0) ∧
      ((traceAnalyticStableInfinityCategory
        .shortComplexOfDistinguishedTriangle
          triangle
          distinguished).map
            (preadditiveCoyoneda.obj leftProbe)).Exact ∧
        ((traceAnalyticStableInfinityCategory
          .shortComplexOfDistinguishedTriangle
            triangle
            distinguished).op.map
              (preadditiveYoneda.obj rightProbe)).Exact :=
  And.intro
    (And.intro
      (traceAnalyticStableInfinityCategory
        .distinguishedTriangle_mor₁_comp_mor₂
        triangle
        distinguished)
      (And.intro
        (traceAnalyticStableInfinityCategory
          .distinguishedTriangle_mor₂_comp_mor₃
          triangle
          distinguished)
        (traceAnalyticStableInfinityCategory
          .distinguishedTriangle_mor₃_comp_shift_mor₁
          triangle
          distinguished)))
    (And.intro
      (traceAnalyticStableInfinityCategory
        .coyonedaShortComplex_exact
        triangle
        distinguished
        leftProbe)
      (traceAnalyticStableInfinityCategory
        .yonedaShortComplex_exact
        triangle
        distinguished
        rightProbe))

end AnalyticMotives
end LFunctions
end Boundary
