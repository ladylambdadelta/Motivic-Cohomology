import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.ShortComplex.Owner

/-!
# Projections for homotopy quotient short complexes

This file exposes projection names for the maps and zero field of the short
complex attached to the homotopy quotient image of an additive distinguished
triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- Projection form of the first map of the short complex attached to a
homotopy quotient image. -/
theorem homotopyQuotientFunctor_shortComplex_firstMap
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).f =
      ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₁ :=
  TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_shortComplex_f triangle distinguished

/-- Projection form of the second map of the short complex attached to a
homotopy quotient image. -/
theorem homotopyQuotientFunctor_shortComplex_secondMap
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).g =
      ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₂ :=
  TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_shortComplex_g triangle distinguished

/-- Projection form of the zero field of the short complex attached to a
homotopy quotient image. -/
theorem homotopyQuotientFunctor_shortComplex_zeroField
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).zero =
      TraceAnalyticStableInfinityCategory
        .homotopyQuotientFunctor_distinguished_mor₁_comp_mor₂
          triangle
          distinguished :=
  TraceAnalyticStableInfinityCategory
    .homotopyQuotientFunctor_shortComplex_zero triangle distinguished

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
