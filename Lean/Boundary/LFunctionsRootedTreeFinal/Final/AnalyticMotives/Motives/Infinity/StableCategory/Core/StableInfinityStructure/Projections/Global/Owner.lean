import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Projections.Owner

/-!
# Global stability projections from the stable-infinity structure certificate

This file exposes the global stability consequences carried by the actual
analytic stable-infinity structure certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The actual stable-infinity certificate supplies compatible distinguished
cofiber and fiber triangles for every morphism. -/
theorem traceAnalyticStableInfinityCategory_actual_global_cofiber_fiber_triangles
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_cofiberTriangleFor morphism ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
      traceAnalyticStableInfinityCategory_fiberTriangleFor morphism ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
        traceAnalyticStableInfinityCategory_fiberTriangleFor morphism =
          (traceAnalyticStableInfinityCategory_cofiberTriangleFor
            morphism).invRotate :=
  traceAnalyticStableInfinityCategory_actual_global_stability.left
    morphism

/-- The actual stable-infinity certificate supplies zero-composition for every
distinguished triangle. -/
theorem traceAnalyticStableInfinityCategory_actual_global_zero_compositions
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₁ ≫ triangle.mor₂ = 0 ∧
      triangle.mor₂ ≫ triangle.mor₃ = 0 ∧
        triangle.mor₃ ≫ triangle.mor₁⟦(1 : ℤ)⟧' = 0 :=
  traceAnalyticStableInfinityCategory_actual_global_stability
    .right
    .left
    triangle
    distinguished

/-- The actual stable-infinity certificate supplies paired Yoneda exactness
for every distinguished triangle. -/
theorem traceAnalyticStableInfinityCategory_actual_global_yoneda_exact
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
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
  traceAnalyticStableInfinityCategory_actual_global_stability
    .right
    .right
    .left
    triangle
    distinguished
    leftProbe
    rightProbe

/-- The actual stable-infinity certificate supplies the current full
per-morphism stability fragment uniformly. -/
theorem traceAnalyticStableInfinityCategory_actual_global_current_full_stability
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_current_full_stability_fragment
      morphism
      leftProbe
      rightProbe :=
  traceAnalyticStableInfinityCategory_actual_global_stability
    .right
    .right
    .right
    .left
    morphism
    leftProbe
    rightProbe

/-- The actual stable-infinity certificate supplies distinguishedness of
contractible triangles. -/
theorem traceAnalyticStableInfinityCategory_actual_global_contractible_distinguished
    (object : StableInfinityOwner.PresentedCategory) :
    Pretriangulated.contractibleTriangle object ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory_actual_global_stability
    .right
    .right
    .right
    .right
    .left
    object

/-- The actual stable-infinity certificate supplies rotation closure for
distinguished triangles. -/
theorem traceAnalyticStableInfinityCategory_actual_global_rotate_distinguished
    (triangle : StableInfinityOwner.PresentedTriangle) :
    triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles ↔
      triangle.rotate ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory_actual_global_stability
    .right
    .right
    .right
    .right
    .right
    triangle

end AnalyticMotives
end LFunctions
end Boundary
