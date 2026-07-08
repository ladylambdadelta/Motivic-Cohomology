import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.Owner

/-!
# Zero-composition laws for homotopy quotient images

This file completes the zero-composition surface for images of additive
distinguished triangles under the quotient functor into the homotopy category
of the analytic stable-infinity model.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- The first two maps of the homotopy quotient image of an additive
distinguished triangle compose to zero. -/
theorem homotopyQuotientFunctor_distinguished_mor₁_comp_mor₂
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₁ ≫
      ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₂ =
        0 :=
  TraceAnalyticStableInfinityCategory
    .comp_zero₁₂_of_homotopyQuotient_distinguished triangle distinguished

/-- The second and third maps of the homotopy quotient image of an additive
distinguished triangle compose to zero. -/
theorem homotopyQuotientFunctor_distinguished_mor₂_comp_mor₃
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₂ ≫
      ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₃ =
        0 :=
  Pretriangulated.comp_distTriang_mor_zero₂₃
    ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
      .mapTriangle.obj triangle)
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_map_distinguished triangle distinguished)

/-- The third map followed by the shifted first map in the homotopy quotient
image of an additive distinguished triangle is zero. -/
theorem homotopyQuotientFunctor_distinguished_mor₃_comp_shift_mor₁
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₃ ≫
      (((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₁)⟦(1 : ℤ)⟧' =
        0 :=
  Pretriangulated.comp_distTriang_mor_zero₃₁
    ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
      .mapTriangle.obj triangle)
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_map_distinguished triangle distinguished)

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
