import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Projections.Global.Owner

/-!
# Zero-composition projections from the actual global stability certificate

This file peels the three zero-composition laws for distinguished triangles
out of the actual stable-infinity global-stability certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first two maps of a distinguished triangle compose to zero. -/
theorem traceAnalyticStableInfinityCategory_actual_global_mor₁_comp_mor₂
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₁ ≫ triangle.mor₂ = 0 :=
  (traceAnalyticStableInfinityCategory_actual_global_zero_compositions
    triangle
    distinguished).left

/-- The second and third maps of a distinguished triangle compose to zero. -/
theorem traceAnalyticStableInfinityCategory_actual_global_mor₂_comp_mor₃
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₂ ≫ triangle.mor₃ = 0 :=
  (traceAnalyticStableInfinityCategory_actual_global_zero_compositions
    triangle
    distinguished).right.left

/-- The boundary map followed by the shifted first map of a distinguished
triangle composes to zero. -/
theorem traceAnalyticStableInfinityCategory_actual_global_mor₃_comp_shift_mor₁
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.mor₃ ≫ triangle.mor₁⟦(1 : ℤ)⟧' = 0 :=
  (traceAnalyticStableInfinityCategory_actual_global_zero_compositions
    triangle
    distinguished).right.right

end AnalyticMotives
end LFunctions
end Boundary
