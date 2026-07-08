import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.Owner

/-!
# Exactness of bounded analytic distinguished triangles

The three consecutive composites in the underlying triangle of a bounded
distinguished triangle vanish, by the pretriangulated exactness theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

/-- The first two morphisms of a bounded distinguished triangle compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.first_comp_second
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.triangle.mor₁ ≫
        boundedTriangle.triangle.mor₂ =
      0 :=
  comp_distTriang_mor_zero₁₂
    boundedTriangle.triangle
    boundedTriangle.distinguished

/-- The second and third morphisms of a bounded distinguished triangle compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.second_comp_third
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.triangle.mor₂ ≫
        boundedTriangle.triangle.mor₃ =
      0 :=
  comp_distTriang_mor_zero₂₃
    boundedTriangle.triangle
    boundedTriangle.distinguished

/-- The third morphism followed by the shifted first morphism is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.third_comp_shifted_first
    {bound : Nat}
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle bound) :
    boundedTriangle.triangle.mor₃ ≫
        boundedTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  comp_distTriang_mor_zero₃₁
    boundedTriangle.triangle
    boundedTriangle.distinguished

end AnalyticMotives
end LFunctions
end Boundary
