import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Owner

/-!
# Projections from the global stability certificate

This file exposes the fields of the global stable-certificate theorem for the
concrete analytic stable-infinity owner object.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Every morphism has compatible distinguished cofiber and fiber triangles. -/
theorem traceAnalyticStableInfinityCategory_global_cofiber_fiber_triangles
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_cofiberTriangleFor morphism ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
      traceAnalyticStableInfinityCategory_fiberTriangleFor morphism ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles ∧
        traceAnalyticStableInfinityCategory_fiberTriangleFor morphism =
          (traceAnalyticStableInfinityCategory_cofiberTriangleFor
            morphism).invRotate :=
  traceAnalyticStableInfinityCategory_global_stability_certificate.left
    morphism

/-- Distinguished triangles have the three standard zero-composition laws. -/
theorem traceAnalyticStableInfinityCategory_global_zero_compositions
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₁ ≫ triangle.mor₂ = 0 ∧
      triangle.mor₂ ≫ triangle.mor₃ = 0 ∧
        triangle.mor₃ ≫ triangle.mor₁⟦(1 : ℤ)⟧' = 0 :=
  traceAnalyticStableInfinityCategory_global_stability_certificate
    .right
    .left
    triangle
    distinguished

/-- Distinguished triangles are exact after covariant and contravariant
preadditive Yoneda evaluation. -/
theorem traceAnalyticStableInfinityCategory_global_yoneda_exact
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
  traceAnalyticStableInfinityCategory_global_stability_certificate
    .right
    .right
    .left
    triangle
    distinguished
    leftProbe
    rightProbe

/-- The current full per-morphism fiber/cofiber stability fragment is
available uniformly. -/
theorem traceAnalyticStableInfinityCategory_global_current_full_stability
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_current_full_stability_fragment
      morphism
      leftProbe
      rightProbe :=
  traceAnalyticStableInfinityCategory_global_stability_certificate
    .right
    .right
    .right
    .left
    morphism
    leftProbe
    rightProbe

/-- Contractible triangles are distinguished. -/
theorem traceAnalyticStableInfinityCategory_global_contractible_distinguished
    (object : StableInfinityOwner.PresentedCategory) :
    Pretriangulated.contractibleTriangle object ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory_global_stability_certificate
    .right
    .right
    .right
    .right
    .left
    object

/-- Distinguished triangles are closed under rotation. -/
theorem traceAnalyticStableInfinityCategory_global_rotate_distinguished
    (triangle : StableInfinityOwner.PresentedTriangle) :
    triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles ↔
      triangle.rotate ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory_global_stability_certificate
    .right
    .right
    .right
    .right
    .right
    triangle

end AnalyticMotives
end LFunctions
end Boundary
