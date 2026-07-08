import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.ZeroComposition.Owner

/-!
# Short complex of a homotopy quotient image

This file attaches Mathlib's distinguished-triangle short complex to the image
of an additive distinguished triangle under the quotient functor into the
homotopy category of the analytic stable-infinity model.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- The short complex attached to the homotopy quotient image of an additive
distinguished triangle. -/
def homotopyQuotientFunctor_shortComplex
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    ShortComplex TraceAnalyticStableInfinityCategory.HomotopyCategory :=
  Pretriangulated.shortComplexOfDistTriangle
    ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
      .mapTriangle.obj triangle)
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_map_distinguished triangle distinguished)

/-- The first map of the short complex attached to a homotopy quotient image
is the first map of that quotient-image triangle. -/
theorem homotopyQuotientFunctor_shortComplex_f
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
  rfl

/-- The second map of the short complex attached to a homotopy quotient image
is the second map of that quotient-image triangle. -/
theorem homotopyQuotientFunctor_shortComplex_g
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
  rfl

/-- The zero field of the quotient-image short complex is the first
zero-composition law for that quotient image. -/
theorem homotopyQuotientFunctor_shortComplex_zero
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
  rfl

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
