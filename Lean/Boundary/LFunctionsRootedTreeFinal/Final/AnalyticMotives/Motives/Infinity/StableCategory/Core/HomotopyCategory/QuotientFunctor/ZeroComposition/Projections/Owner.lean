import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.ZeroComposition.Owner

/-!
# Projections for quotient-image zero-composition laws

This file exposes the three zero-composition laws for homotopy quotient images
under stable projection names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- Projection form of the first zero-composition law for a quotient image of
an additive distinguished triangle. -/
theorem homotopyQuotientFunctor_zero₁₂
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
    .homotopyQuotientFunctor_distinguished_mor₁_comp_mor₂
      triangle
      distinguished

/-- Projection form of the second zero-composition law for a quotient image of
an additive distinguished triangle. -/
theorem homotopyQuotientFunctor_zero₂₃
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
  TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_distinguished_mor₂_comp_mor₃
      triangle
      distinguished

/-- Projection form of the shifted third zero-composition law for a quotient
image of an additive distinguished triangle. -/
theorem homotopyQuotientFunctor_zero₃₁
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
  TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_distinguished_mor₃_comp_shift_mor₁
      triangle
      distinguished

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
