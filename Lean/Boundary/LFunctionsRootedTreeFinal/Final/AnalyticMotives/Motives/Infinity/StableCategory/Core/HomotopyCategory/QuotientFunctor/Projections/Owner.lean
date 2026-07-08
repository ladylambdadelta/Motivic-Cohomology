import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.Owner

/-!
# Projections for the homotopy-category quotient functor

This file exposes stable projection names for the triangulated quotient
functor from additive analytic homotopy motives into the homotopy category of
the analytic stable-infinity model.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- The homotopy quotient functor's exact functor structure is the Verdier
quotient functor's exact functor structure. -/
theorem homotopyQuotientFunctor_triangulated_stableVerdier_eq :
    TraceAnalyticStableInfinityCategory
        .homotopyQuotientFunctorIsTriangulated =
      TraceAnalyticStableMotiveCategory.quotientFunctorIsTriangulated :=
  TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctorIsTriangulated_eq_stable

/-- Projection form of distinguished-triangle preservation for the homotopy
quotient functor. -/
theorem homotopyQuotientFunctor_preserves_distinguished
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    (TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle ∈
      TraceAnalyticStableInfinityCategory
        .homotopyCategoryDistinguishedTriangles :=
  TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_map_distinguished triangle distinguished

/-- Projection form of the first zero-composite law after applying the
homotopy quotient functor to an additive distinguished triangle. -/
theorem homotopyQuotientFunctor_distinguished_comp_zero₁₂
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

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
